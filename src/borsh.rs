use std::collections::BTreeMap;
use std::io::{Read, Write};

use borsh::{BorshDeserialize, BorshSerialize};
use either::Either;
use num_bigint::{BigInt, BigUint, Sign};
use ton_abi::{ParamType, TokenValue};
use ton_block::{Grams, MsgAddress};

pub struct TokenWrapper<'a>(&'a TokenValue);

impl<'a> BorshSerialize for TokenWrapper<'a> {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        match &self.0 {
            TokenValue::Uint(uint) => {
                let mut number = uint.number.to_bytes_le();
                let number = if uint.size <= MAX_SMALL_INT_SIZE {
                    number.resize(small_int_size(uint.size), 0);
                    number
                } else {
                    let mut buffer = vec![0; (uint.size + 7) / 8];
                    for (l, r) in buffer.iter_mut().rev().zip(number.into_iter()) {
                        *l = r;
                    }
                    buffer
                };
                writer.write(&number)?;
                Ok(())
            }
            TokenValue::Int(int) => {
                let mut number = int.number.to_signed_bytes_le();
                let padding: u8 = if int.number.sign() == Sign::Minus {
                    0xff
                } else {
                    0
                };

                let number = if int.size <= MAX_SMALL_INT_SIZE {
                    number.resize(small_int_size(int.size), padding);
                    number
                } else {
                    let mut buffer = vec![padding; (int.size + 7) / 8];
                    for (l, r) in buffer.iter_mut().rev().zip(number.into_iter()) {
                        *l = r;
                    }
                    buffer
                };
                writer.write(&number)?;
                Ok(())
            }
            TokenValue::VarInt(_, int) => {
                let bytes = int.to_signed_bytes_le();
                let mut number = Vec::with_capacity(1 + bytes.len());
                number.push(bytes.len() as u8);
                number.extend_from_slice(&bytes);
                writer.write(&number)?;
                Ok(())
            }
            TokenValue::VarUint(_, uint) => {
                let bytes = uint.to_bytes_le();
                let mut number = Vec::with_capacity(1 + bytes.len());
                number.push(bytes.len() as u8);
                number.extend_from_slice(&bytes);
                writer.write(&number)?;
                Ok(())
            }
            TokenValue::Bool(bool) => bool.serialize(writer),
            TokenValue::Tuple(tuple) => {
                for token in tuple {
                    TokenWrapper(&token.value).serialize(writer)?;
                }
                Ok(())
            }
            TokenValue::Array(_, vec) => {
                let size = vec.len() as u32;
                size.serialize(writer)?;
                for item in vec {
                    TokenWrapper(item).serialize(writer)?;
                }
                Ok(())
            }
            TokenValue::FixedArray(_, vec) => {
                for item in vec {
                    TokenWrapper(item).serialize(writer)?;
                }
                Ok(())
            }
            TokenValue::Cell(cell) => {
                let cell_bytes = ton_types::serialize_toc(cell)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
                cell_bytes.serialize(writer)
            }
            TokenValue::Map(key_type, _, map) => {
                let size = map.len() as u32;
                size.serialize(writer)?;
                for (item, value) in map {
                    let key = ton_abi::token::Tokenizer::tokenize_parameter(
                        key_type,
                        &item.clone().into(),
                    )
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
                    TokenWrapper(&key).serialize(writer)?;
                    TokenWrapper(value).serialize(writer)?;
                }
                Ok(())
            }
            TokenValue::Address(add) => {
                match add {
                    MsgAddress::AddrStd(ad) => {
                        0u8.serialize(writer)?; //discriminant
                        ad.workchain_id.serialize(writer)?;
                        let address: Vec<u8> = ad.address.get_bytestring(0);
                        writer.write_all(&address)
                    }
                    _ => Err(std::io::Error::new(
                        std::io::ErrorKind::Other,
                        "Invalid address",
                    )),
                }
            }
            TokenValue::Bytes(bytes) => bytes.serialize(writer),
            TokenValue::FixedBytes(bytes) => writer.write_all(bytes),
            TokenValue::String(str) => str.serialize(writer),
            TokenValue::Token(token) => {
                let value = token.0;
                value.serialize(writer)
            }
            TokenValue::Time(time) => time.serialize(writer),
            TokenValue::Expire(exp) => exp.serialize(writer),
            TokenValue::PublicKey(pubkey) => pubkey.map(|pk| pk.to_bytes()).serialize(writer),
            TokenValue::Optional(_, val) => match val {
                None => 0u8.serialize(writer),
                Some(a) => {
                    1u8.serialize(writer)?;
                    TokenWrapper(a).serialize(writer)
                }
            },
            TokenValue::Ref(val) => TokenWrapper(val).serialize(writer),
        }
    }
}

const MAX_SMALL_INT_SIZE: usize = 128;

fn small_int_size(size: usize) -> usize {
    match size {
        0..=8 => 1,
        9..=16 => 2,
        17..=32 => 4,
        33..=64 => 8,
        _ => 16,
    }
}

fn read_any_int(buf: &mut &[u8], size: usize, signed: bool) -> anyhow::Result<TokenValue> {
    let any_int = match size {
        0..=8 => {
            if signed {
                Either::Left(BigInt::from(i8::deserialize(buf)?))
            } else {
                Either::Right(BigUint::from(u8::deserialize(buf)?))
            }
        }
        9..=16 => {
            if signed {
                Either::Left(BigInt::from(i16::deserialize(buf)?))
            } else {
                Either::Right(BigUint::from(u16::deserialize(buf)?))
            }
        }
        17..=32 => {
            if signed {
                Either::Left(BigInt::from(i32::deserialize(buf)?))
            } else {
                Either::Right(BigUint::from(u32::deserialize(buf)?))
            }
        }
        33..=64 => {
            if signed {
                Either::Left(BigInt::from(i64::deserialize(buf)?))
            } else {
                Either::Right(BigUint::from(u64::deserialize(buf)?))
            }
        }
        65..=128 => {
            let mut bytes = [0; 16];
            buf.read_exact(&mut bytes)?;

            if signed {
                Either::Left(BigInt::from_signed_bytes_le(&bytes))
            } else {
                Either::Right(BigUint::from_bytes_le(&bytes))
            }
        }
        _ => {
            let mut bytes = [0; 32];
            let bytes = &mut bytes[..(size + 7) / 8];
            buf.read_exact(bytes)?;

            if signed {
                Either::Left(BigInt::from_signed_bytes_be(&bytes))
            } else {
                Either::Right(BigUint::from_bytes_be(&bytes))
            }
        }
    };

    Ok(match any_int {
        Either::Left(a) => TokenValue::Int(ton_abi::Int {
            number: a,
            size: size as usize,
        }),
        Either::Right(b) => TokenValue::Uint(ton_abi::Uint {
            number: b,
            size: size as usize,
        }),
    })
}

pub struct TokenWrapperOwned(TokenValue);

impl BorshSerialize for TokenWrapperOwned {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let wrapped = TokenWrapper(&self.0);
        wrapped.serialize(writer)
    }
}

pub fn serialize_tokens(tokens: &[TokenValue]) -> anyhow::Result<Vec<u8>> {
    let tokens_wrapped = tokens.iter().map(|t| TokenWrapperOwned(t.clone()));
    let mut writer = Vec::with_capacity(128);
    for token in tokens_wrapped {
        token.serialize(&mut writer)?;
    }

    Ok(writer)
}

pub fn deserialize_with_abi(
    reader: &mut &[u8],
    types: &[ParamType],
) -> anyhow::Result<Vec<TokenValue>> {
    let mut tokens = Vec::with_capacity(types.len());

    for ty in types {
        let token = deserialize(reader, ty)?;
        tokens.push(token);
    }

    Ok(tokens)
}

pub fn deserialize(reader: &mut &[u8], ty: &ParamType) -> anyhow::Result<TokenValue> {
    match ty {
        ParamType::Uint(size) => read_any_int(reader, *size, false),
        ParamType::Int(size) => read_any_int(reader, *size, true),
        ParamType::VarUint(size) => read_any_int(reader, *size, false),
        ParamType::VarInt(size) => read_any_int(reader, *size, true),
        ParamType::Bool => {
            let bool = bool::deserialize(reader)?;
            Ok(TokenValue::Bool(bool))
        }
        ParamType::Tuple(a) => {
            let mut tokens = Vec::with_capacity(a.len());
            for token in a {
                let value = deserialize(reader, &token.kind)?;
                let token = ton_abi::Token::new(&token.name, value);
                tokens.push(token);
            }
            Ok(TokenValue::Tuple(tokens))
        }
        ParamType::Array(ty) => {
            let size: u32 = u32::deserialize(reader)?;
            let mut tokens = Vec::with_capacity(size as usize);
            for _ in 0..size {
                let value = deserialize(reader, ty)?;
                tokens.push(value);
            }
            Ok(TokenValue::Array(*ty.clone(), tokens))
        }
        ParamType::FixedArray(ty, size) => {
            let mut tokens = Vec::with_capacity(*size);
            for _ in 0..*size {
                let value = deserialize(reader, ty)?;
                tokens.push(value);
            }
            Ok(TokenValue::FixedArray(*ty.clone(), tokens))
        }
        ParamType::Cell => {
            let bytes = Vec::deserialize(reader)?;
            let cell = ton_types::deserialize_tree_of_cells(&mut &bytes[..])?;
            Ok(TokenValue::Cell(cell))
        }
        ParamType::Map(a, b) => {
            let size = u32::deserialize(reader)?;
            let mut tokens = BTreeMap::new();
            for _ in 0..size {
                let key = deserialize(reader, a)?.to_string();
                let value = deserialize(reader, b)?;
                tokens.insert(key, value);
            }
            Ok(TokenValue::Map(*a.clone(), *b.clone(), tokens))
        }
        ParamType::Address => {
            let ty: u8 = u8::deserialize(reader)?;
            if ty == 0 {
                let wc: i8 = i8::deserialize(reader)?;
                let address = <[u8; 32] as BorshDeserialize>::deserialize(reader)?;

                let address = ton_block::MsgAddrStd::with_address(None, wc, address.into());
                Ok(TokenValue::Address(MsgAddress::AddrStd(address)))
            } else {
                anyhow::bail!("unsupported address type")
            }
        }
        ParamType::Bytes => {
            let bytes = Vec::deserialize(reader)?;
            Ok(TokenValue::Bytes(bytes))
        }
        ParamType::FixedBytes(size) => {
            let mut buf = vec![0; *size as usize];
            reader.read_exact(&mut buf)?;
            Ok(TokenValue::FixedBytes(buf))
        }
        ParamType::String => {
            let string = String::deserialize(reader)?;
            Ok(TokenValue::String(string))
        }
        ParamType::Token => {
            let amount = u128::deserialize(reader)?;
            Ok(TokenValue::Token(Grams(amount)))
        }
        ParamType::Time => {
            let time = u64::deserialize(reader)?;
            Ok(TokenValue::Time(time))
        }
        ParamType::Expire => {
            let expire = u32::deserialize(reader)?;
            Ok(TokenValue::Expire(expire))
        }
        ParamType::PublicKey => {
            let bytes: Option<[u8; 32]> = BorshDeserialize::deserialize(reader)?;
            let pubkey = bytes
                .map(|x| ed25519_dalek::PublicKey::from_bytes(&x))
                .transpose()?;
            Ok(TokenValue::PublicKey(pubkey))
        }
        ParamType::Optional(ty) => {
            let is_set = bool::deserialize(reader)?;
            if is_set {
                let value = deserialize(reader, ty)?;
                Ok(TokenValue::Optional(*ty.clone(), Some(Box::new(value))))
            } else {
                Ok(TokenValue::Optional(*ty.clone(), None))
            }
        }
        ParamType::Ref(a) => {
            let value = deserialize(reader, a)?;
            Ok(TokenValue::Ref(Box::new(value)))
        }
    }
}

#[cfg(test)]
mod test {
    use paste::paste;
    use std::str::FromStr;
    use ton_block::MsgAddressInt;

    use super::*;

    macro_rules! generate_test {
        ($size:literal, $buf:ident, $number:ident) => {
            let mut $buf = vec![];
            paste! {
                generate_test!(@signed i, $size,  [<i $size>]::MAX, $buf, $number);
                assert_eq!(read_any_int(&mut &$buf[..], $size as usize, true).unwrap(), $number);
                $buf.clear();

                generate_test!(@signed i, $size, [<i $size>]::MIN, $buf, $number);
                assert_eq!(read_any_int(&mut &$buf[..], $size as usize, true).unwrap(), $number);
                $buf.clear();

                generate_test!(@signed i, $size, 0, $buf, $number);
                assert_eq!(read_any_int(&mut &$buf[..], $size as usize, true).unwrap(), $number);
                $buf.clear();

                generate_test!(@signed u, $size, [<u $size>]::MAX, $buf, $number);
                assert_eq!(read_any_int(&mut &$buf[..], $size as usize, false).unwrap(), $number);
                $buf.clear();

                generate_test!(@signed u, $size, [<u $size>]::MIN, $buf, $number);
                assert_eq!(read_any_int(&mut &$buf[..], $size as usize, false).unwrap(), $number);
                $buf.clear();

                generate_test!(@signed u, $size, 0, $buf, $number);
                assert_eq!(read_any_int(&mut &$buf[..], $size as usize, false).unwrap(), $number);
                $buf.clear();
            }
        };
        (@signed i, $size:literal, $num:expr, $buf:ident, $number:ident) => {
            paste! {
                let $number = ton_abi::TokenValue::Int(
                    ton_abi::Int {
                        number: BigInt::from($num as [<i $size>]),
                        size: $size as usize,
                    }
                );
                TokenWrapper(&$number).serialize(&mut $buf).unwrap();
            }
        };
        (@signed u,  $size:literal, $num:expr, $buf:ident, $number:ident) => {
            paste! {
                let $number = ton_abi::TokenValue::Uint(
                    ton_abi::Uint {
                        number: BigUint::from($num as [<u $size>]),
                        size: $size as usize,
                    }
                );
                TokenWrapper(&$number).serialize(&mut $buf).unwrap();
            }
        };
    }

    #[test]
    fn test_ints() {
        generate_test!(8, buf, num_name);
        generate_test!(16, buf, num_name);
        generate_test!(32, buf, num_name);
        generate_test!(64, buf, num_name);
        generate_test!(128, buf, num_name);
    }

    #[test]
    fn test_address() {
        let addr = match MsgAddressInt::from_str(
            "0:8e2586602513e99a55fa2be08561469c7ce51a7d5a25977558e77ef2bc9387b4",
        )
        .unwrap()
        {
            MsgAddressInt::AddrStd(x) => x,
            _ => panic!("wrong address"),
        };
        let token = TokenValue::Address(MsgAddress::AddrStd(addr));
        let tokens = vec![token];
        let packed = super::serialize_tokens(&tokens).unwrap();
        dbg!(&packed);
        let unpacked =
            super::deserialize_with_abi(&mut &packed[..], &[ParamType::Address]).unwrap();

        assert_eq!(unpacked, tokens);
    }

    #[test]
    fn test_huge_ints() {
        let uint = ton_abi::Uint {
            number: BigUint::from(u128::MAX),
            size: 256,
        };
        let bytes = serialize_tokens(&[TokenValue::Uint(uint.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Uint(256)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Uint(uint).to_string());

        let uint = ton_abi::Uint {
            number: BigUint::from(u128::MIN),
            size: 256,
        };
        let bytes = serialize_tokens(&[TokenValue::Uint(uint.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Uint(256)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Uint(uint).to_string());

        let uint = ton_abi::Uint {
            number: BigUint::from(1u128),
            size: 256,
        };
        let bytes = serialize_tokens(&[TokenValue::Uint(uint.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Uint(256)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Uint(uint).to_string());

        let uint = ton_abi::Uint {
            number: BigUint::from(1u128),
            size: 123,
        };
        let bytes = serialize_tokens(&[TokenValue::Uint(uint.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Uint(123)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Uint(uint).to_string());
        //ints
        let int = ton_abi::Int {
            number: BigInt::from(i128::max_value()),
            size: 256,
        };
        let bytes = serialize_tokens(&[TokenValue::Int(int.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Int(256)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Int(int).to_string());

        let int = ton_abi::Int {
            number: BigInt::from(i128::min_value() + 1),
            size: 256,
        };
        let bytes = serialize_tokens(&[TokenValue::Int(int.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Int(256)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Int(int).to_string());

        let int = ton_abi::Int {
            number: BigInt::from(1i128),
            size: 256,
        };
        let bytes = serialize_tokens(&[TokenValue::Int(int.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Int(256)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Int(int).to_string());

        let int = ton_abi::Int {
            number: BigInt::from(1i128),
            size: 123,
        };
        let bytes = serialize_tokens(&[TokenValue::Int(int.clone())]).unwrap();
        let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Int(123)])
            .unwrap()
            .remove(0);
        assert_eq!(got.to_string(), TokenValue::Int(int).to_string());
    }

    #[test]
    fn test_complex() {
        for i in 1..32 {
            let bytes = vec![1; i];
            let uint = ton_abi::Uint {
                number: BigUint::from_bytes_le(&bytes),
                size: 256,
            };
            let bytes = serialize_tokens(&[TokenValue::Uint(uint.clone())]).unwrap();
            let got = deserialize_with_abi(&mut &bytes[..], &[ParamType::Uint(256)])
                .unwrap()
                .remove(0);
            assert_eq!(got.to_string(), TokenValue::Uint(uint).to_string());
        }
    }
}
