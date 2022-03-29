use std::collections::BTreeMap;
use std::convert::TryInto;
use std::io::{Read, Write};

use anyhow::Context;
use borsh::{BorshDeserialize, BorshSerialize};
use either::Either;
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;
use ton_abi::{ParamType, TokenValue};
use ton_block::{Deserializable, Grams, MsgAddress};
use ton_types::Cell;

pub struct TokenWrapper<'a>(&'a ton_abi::TokenValue);

impl<'a> BorshSerialize for TokenWrapper<'a> {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        match &self.0 {
            TokenValue::Uint(uint) => {
                map_any_int(writer, uint.number.clone(), false, uint.size, || {
                    uint.number.to_bytes_le()
                })?;
            }
            TokenValue::Int(int) => {
                map_any_int(writer, int.number.clone(), true, int.size, || {
                    int.number.to_signed_bytes_le()
                })?;
            }
            TokenValue::VarInt(size, int) => map_any_int(writer, int.clone(), true, *size, || {
                int.to_signed_bytes_le()
            })?,
            TokenValue::VarUint(size, uint) => {
                map_any_int(writer, uint.clone(), false, *size, || uint.to_bytes_le())?;
            }
            TokenValue::Bool(bool) => {
                bool.serialize(writer)?;
            }
            TokenValue::Tuple(tuple) => {
                for token in tuple {
                    let token = TokenWrapper(&token.value);
                    token.serialize(writer)?;
                }
            }
            TokenValue::Array(_, vec) => {
                let size = vec.len() as u32;
                size.serialize(writer)?;

                for item in vec {
                    (TokenWrapper(item)).serialize(writer)?;
                }
            }
            TokenValue::FixedArray(_, vec) => {
                for item in vec {
                    (TokenWrapper(item)).serialize(writer)?;
                }
            }
            TokenValue::Cell(cell) => {
                let cell_bytes = ton_block::Serializable::write_to_bytes(cell)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
                cell_bytes.serialize(writer)?;
            }
            TokenValue::Map(_, _, map) => {
                map.len().serialize(writer)?;
                todo!("types");
                for (key, value) in map.iter() {
                    key.serialize(writer)?;
                    TokenWrapper(value).serialize(writer)?;
                }
            }
            TokenValue::Address(add) => {
                match add {
                    MsgAddress::AddrStd(ad) => {
                        0u8.serialize(writer)?; //discriminant
                        ad.workchain_id.serialize(writer)?;
                        let addr = ton_block::Serializable::write_to_bytes(&ad.address)
                            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
                        addr.serialize(writer)?;
                    }
                    _ => {
                        return Err(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            "Invalid address",
                        ))
                    }
                };
            }
            TokenValue::Bytes(bytes) => {
                bytes.serialize(writer)?;
            }
            TokenValue::FixedBytes(bytes) => {
                writer.write_all(&bytes)?;
            }
            TokenValue::String(str) => {
                str.serialize(writer)?;
            }
            TokenValue::Token(token) => {
                let value = token.0;
                value.serialize(writer)?;
            }
            TokenValue::Time(time) => {
                time.serialize(writer)?;
            }
            TokenValue::Expire(exp) => {
                exp.serialize(writer)?;
            }
            TokenValue::PublicKey(pubkey) => {
                pubkey.map(|pk| pk.to_bytes()).serialize(writer)?;
            }
            TokenValue::Optional(_, val) => match val {
                None => {
                    0u8.serialize(writer)?;
                }
                Some(a) => {
                    1u8.serialize(writer)?;
                    TokenWrapper(a).serialize(writer)?;
                }
            },
            TokenValue::Ref(val) => {
                TokenWrapper(val).serialize(writer)?;
            }
        }
        Ok(())
    }
}

fn map_any_int<W, F>(
    writer: &mut W,
    any_int: impl ToPrimitive,
    signed: bool,
    size: usize,
    bytes_factory: F,
) -> std::io::Result<()>
where
    W: Write,
    F: FnOnce() -> Vec<u8>,
{
    use std::io;
    let size = size
        .try_into()
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "Invalid size for integer"))?;
    map_any_int_inner(writer, any_int, signed, size, bytes_factory)
        .with_context(|| format!("Size: {}", size))
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))
}

fn map_any_int_inner<W, F>(
    writer: &mut W,
    any_int: impl ToPrimitive,
    signed: bool,
    size: u16,
    bytes_factory: F,
) -> anyhow::Result<()>
where
    W: Write,
    F: FnOnce() -> Vec<u8>,
{
    // Don't edit it's a generated code
    match size {
        0..=8 => {
            if signed {
                any_int
                    .to_i8()
                    .context("Bad signed integer")?
                    .serialize(writer)?
            } else {
                any_int
                    .to_u8()
                    .context("Bad unsigned integer")?
                    .serialize(writer)?
            }
        }
        9..=16 => {
            if signed {
                any_int
                    .to_i16()
                    .context("Bad signed integer")?
                    .serialize(writer)?
            } else {
                any_int
                    .to_u16()
                    .context("Bad unsigned integer")?
                    .serialize(writer)?
            }
        }
        17..=32 => {
            if signed {
                any_int
                    .to_i32()
                    .context("Bad signed integer")?
                    .serialize(writer)?
            } else {
                any_int
                    .to_u32()
                    .context("Bad unsigned integer")?
                    .serialize(writer)?
            }
        }
        33..=64 => {
            if signed {
                any_int
                    .to_i64()
                    .context("Bad signed integer")?
                    .serialize(writer)?
            } else {
                any_int
                    .to_u64()
                    .context("Bad unsigned integer")?
                    .serialize(writer)?
            }
        }
        65..=128 => {
            if signed {
                any_int
                    .to_i128()
                    .context("Bad signed integer")?
                    .serialize(writer)?
            } else {
                any_int
                    .to_u128()
                    .context("Bad unsigned integer")?
                    .serialize(writer)?
            }
        }
        _ => {
            bytes_factory().serialize(writer)?;
        }
    };

    Ok(())
}

fn read_any_int(buf: &mut &[u8], size: usize, signed: bool) -> anyhow::Result<ton_abi::TokenValue> {
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
            if signed {
                Either::Left(BigInt::from(i128::deserialize(buf)?))
            } else {
                Either::Right(BigUint::from(u128::deserialize(buf)?))
            }
        }
        _ => {
            if signed {
                Either::Left(BigInt::from_signed_bytes_le(buf))
            } else {
                Either::Right(BigUint::from_bytes_le(buf))
            }
        }
    };

    Ok(match any_int {
        Either::Left(a) => ton_abi::TokenValue::Int(ton_abi::Int {
            number: a,
            size: size as usize,
        }),
        Either::Right(b) => ton_abi::TokenValue::Uint(ton_abi::Uint {
            number: b,
            size: size as usize,
        }),
    })
}

pub struct TokenWrapperOwned(ton_abi::TokenValue);

impl BorshSerialize for TokenWrapperOwned {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let wrapped = TokenWrapper(&self.0);
        wrapped.serialize(writer)
    }
}

pub fn serialize_tokens(tokens: &[ton_abi::TokenValue]) -> anyhow::Result<Vec<u8>> {
    let tokens_wrapped = tokens
        .iter()
        .map(|t| TokenWrapperOwned(t.clone()))
        .collect::<Vec<_>>();
    let serialized = borsh::BorshSerialize::try_to_vec(&tokens_wrapped)?;

    Ok(serialized)
}

pub fn deserialize_with_abi(
    reader: &mut &[u8],
    types: &[ton_abi::ParamType],
) -> anyhow::Result<Vec<ton_abi::TokenValue>> {
    let mut tokens = Vec::with_capacity(types.len());

    for ty in types {
        let token = deserialize(reader, ty)?;
        tokens.push(token);
    }

    Ok(tokens)
}

pub fn deserialize(reader: &mut &[u8], ty: &ton_abi::ParamType) -> anyhow::Result<TokenValue> {
    match ty {
        ParamType::Uint(size) => {
            let value = read_any_int(reader, *size, false)?;
            Ok(value)
        }
        ParamType::Int(size) => {
            let value = read_any_int(reader, *size, true)?;
            Ok(value)
        }
        ParamType::VarUint(size) => {
            let value = read_any_int(reader, *size, false)?;
            Ok(value)
        }
        ParamType::VarInt(size) => {
            let value = read_any_int(reader, *size, true)?;
            Ok(value)
        }
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
            let bytes: Vec<u8> = Vec::deserialize(reader)?;
            let cell = Cell::construct_from_bytes(&bytes)?;
            Ok(TokenValue::Cell(cell))
        }
        ParamType::Map(a, b) => {
            let size: u32 = u32::deserialize(reader)?;
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
                let address = Vec::<u8>::deserialize(reader)?;

                let address = ton_block::MsgAddrStd::with_address(None, wc, address.into());
                Ok(TokenValue::Address(ton_block::MsgAddress::AddrStd(address)))
            } else {
                anyhow::bail!("unsupported address type")
            }
        }
        ParamType::Bytes => {
            let bytes: Vec<u8> = Vec::deserialize(reader)?;
            Ok(TokenValue::Bytes(bytes))
        }
        ParamType::FixedBytes(size) => {
            let mut buf = Vec::with_capacity(*size);
            reader.read_exact(&mut buf)?;
            Ok(TokenValue::Bytes(buf))
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
            let bytes: core::option::Option<Vec<u8>> = BorshDeserialize::deserialize(reader)?;
            let bytes = bytes.and_then(|x| ed25519_dalek::PublicKey::from_bytes(&x).ok());

            Ok(TokenValue::PublicKey(bytes))
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
                let $number =  ton_abi::TokenValue::Int(
                    ton_abi::Int {
                        number: BigInt::from($num as [<i $size>]),
                        size: $size as usize,
                    });
                map_any_int(&mut $buf,  BigInt::from($num as [<i $size>]), true, $size, || {
                   BigInt::from($num as [<u $size>]).to_signed_bytes_le()
                }).unwrap();
            }
        };
        (@signed u,  $size:literal, $num:expr, $buf:ident, $number:ident) => {
            paste! {
                let $number =  ton_abi::TokenValue::Uint(
                    ton_abi::Uint {
                        number: BigUint::from($num as [<u $size>]),
                        size: $size as usize,
                    });
                map_any_int(&mut $buf, BigUint::from($num as [<u $size>]), false, $size, || {
                   BigUint::from($num as [<u $size>]).to_bytes_le()
                }).unwrap();
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
}
