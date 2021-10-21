use anyhow::Result;

use crate::AbiMappingError;

pub fn decode_ton_event_abi(abi: &str) -> Result<Vec<ton_abi::Param>> {
    let params = serde_json::from_str::<Vec<ton_abi::Param>>(abi)?;
    Ok(params)
}

pub fn unpack_from_cell(
    params: &[ton_abi::Param],
    mut cursor: ton_types::SliceData,
) -> Result<Vec<ton_abi::Token>> {
    let mut tokens = Vec::new();

    for param in params {
        let last = Some(param) == params.last();
        let (token_value, new_cursor) =
            ton_abi::TokenValue::read_from(&param.kind, cursor, last, 2)?;

        cursor = new_cursor;
        tokens.push(ton_abi::Token {
            name: param.name.clone(),
            value: token_value,
        });
    }

    if cursor.remaining_references() != 0 || cursor.remaining_bits() != 0 {
        Err(AbiMappingError::IncompleteDeserialization.into())
    } else {
        Ok(tokens)
    }
}

pub fn map_ton_tokens_to_eth_bytes(
    tokens: Vec<ton_abi::Token>,
) -> Result<Vec<u8>, AbiMappingError> {
    let tokens = tokens
        .into_iter()
        .map(|token| token.value)
        .map(map_ton_token_to_eth)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ethabi::encode(&tokens))
}

fn map_ton_token_to_eth(token: ton_abi::TokenValue) -> Result<ethabi::Token, AbiMappingError> {
    Ok(match token {
        ton_abi::TokenValue::FixedBytes(bytes) => ethabi::Token::FixedBytes(bytes),
        ton_abi::TokenValue::Bytes(bytes) => ethabi::Token::Bytes(bytes),
        ton_abi::TokenValue::Uint(a) => {
            let bytes = a.number.to_bytes_le();
            ethabi::Token::Uint(ethabi::Uint::from_little_endian(&bytes))
        }
        ton_abi::TokenValue::Int(a) => {
            let mut bytes = a.number.to_signed_bytes_le();
            let sign = bytes
                .last()
                .map(|first| (first >> 7) * 255)
                .unwrap_or_default();
            bytes.resize(32, sign);
            ethabi::Token::Int(ethabi::Int::from_little_endian(&bytes))
        }
        ton_abi::TokenValue::Bool(a) => ethabi::Token::Bool(a),
        ton_abi::TokenValue::FixedArray(_, tokens) => ethabi::Token::FixedArray(
            tokens
                .into_iter()
                .map(map_ton_token_to_eth)
                .collect::<Result<_, _>>()?,
        ),
        ton_abi::TokenValue::Array(_, tokens) => ethabi::Token::Array(
            tokens
                .into_iter()
                .map(map_ton_token_to_eth)
                .collect::<Result<_, _>>()?,
        ),
        ton_abi::TokenValue::Tuple(tokens) => ethabi::Token::Tuple(
            tokens
                .into_iter()
                .map(|ton| map_ton_token_to_eth(ton.value))
                .collect::<Result<_, _>>()?,
        ),
        ton_abi::TokenValue::String(a) => ethabi::Token::String(a),
        any => return Err(AbiMappingError::UnsupportedTonType(any)),
    })
}
