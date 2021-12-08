use anyhow::Result;
use num_bigint::{BigInt, BigUint};
use serde::Deserialize;

use crate::AbiMappingError;

pub struct EthEventAbi {
    topic_hash: ethabi::Hash,
    params: Vec<ethabi::ParamType>,
}

impl EthEventAbi {
    pub fn new(abi: &str) -> Result<Self> {
        let event = decode_eth_event_abi(abi)?;
        let params = event.inputs.iter().map(|item| item.kind.clone()).collect();
        let topic_hash = event.signature();
        Ok(Self { topic_hash, params })
    }

    pub fn get_eth_topic_hash(&self) -> &ethabi::Hash {
        &self.topic_hash
    }

    pub fn decode_and_map(&self, data: &[u8]) -> Result<ton_types::Cell> {
        let tokens = ethabi::decode(&self.params, data)?;
        map_eth_tokens_to_ton_cell(tokens, &self.params)
    }
}

pub fn decode_eth_event_abi(abi: &str) -> Result<ethabi::Event> {
    #[derive(Deserialize)]
    #[serde(untagged)]
    pub enum Operation {
        Event(ethabi::Event),
    }

    serde_json::from_str::<Operation>(abi)
        .map(|item| match item {
            Operation::Event(event) => event,
        })
        .map_err(anyhow::Error::from)
}

pub fn map_eth_abi_to_ton<'a, I>(abi: I, can_update_ctx: bool) -> Result<Vec<ton_abi::ParamType>>
where
    I: Iterator<Item = &'a ethabi::ParamType>,
{
    abi.filter_map(|param| map_eth_abi_param_to_ton(param, can_update_ctx).transpose())
        .collect()
}

fn map_eth_abi_param_to_ton(
    param: &ethabi::ParamType,
    can_update_ctx: bool,
) -> Result<Option<ton_abi::ParamType>> {
    Ok(Some(match param {
        ethabi::ParamType::Address => ton_abi::ParamType::Bytes,
        ethabi::ParamType::Bytes => ton_abi::ParamType::Bytes,
        ethabi::ParamType::Int(size) => ton_abi::ParamType::Int(*size),
        ethabi::ParamType::Uint(size) => ton_abi::ParamType::Uint(*size),
        ethabi::ParamType::Bool => ton_abi::ParamType::Bool,
        ethabi::ParamType::String => ton_abi::ParamType::String,
        ethabi::ParamType::Array(param) => match map_eth_abi_param_to_ton(param.as_ref(), false)? {
            Some(param) => ton_abi::ParamType::Array(Box::new(param)),
            None => return Ok(None),
        },
        &ethabi::ParamType::FixedBytes(1) if can_update_ctx => return Ok(None),
        ethabi::ParamType::FixedBytes(size) => ton_abi::ParamType::FixedBytes(*size),
        ethabi::ParamType::FixedArray(param, size) => {
            match map_eth_abi_param_to_ton(param.as_ref(), false)? {
                Some(param) => ton_abi::ParamType::FixedArray(Box::new(param), *size),
                None => return Ok(None),
            }
        }
        ethabi::ParamType::Tuple(params) => ton_abi::ParamType::Tuple(
            params
                .iter()
                .filter_map(|item| {
                    map_eth_abi_param_to_ton(item, can_update_ctx)
                        .transpose()
                        .map(|kind| {
                            kind.map(|kind| ton_abi::Param {
                                name: String::new(),
                                kind,
                            })
                        })
                })
                .collect::<Result<Vec<ton_abi::Param>>>()?,
        ),
    }))
}

pub fn map_eth_tokens_to_ton_cell(
    tokens: Vec<ethabi::Token>,
    abi: &[ethabi::ParamType],
) -> Result<ton_types::Cell> {
    let mut ctx = EthToTonMappingContext::default();

    let tokens = tokens
        .into_iter()
        .zip(abi.iter())
        .filter_map(|(token, param)| map_eth_token_to_ton(token, param, true, &mut ctx).transpose())
        .collect::<Result<Vec<ton_abi::TokenValue>>>()?;

    let cells = Vec::with_capacity(tokens.len());
    ton_abi::TokenValue::pack_token_values_into_chain(
        &tokens,
        cells,
        ton_abi::contract::ABI_VERSION_2_1,
    )
    .and_then(|builder| builder.into_cell())
}

#[derive(Default, Copy, Clone, Deserialize)]
pub struct EthToTonMappingContext {
    /// Starts new cell for each tuple.
    ///
    /// See `MAPPING_FLAG_TUPLES_TO_NEW_CELL`
    pub tuples_to_new_cell: bool,

    /// Interprets bytes ad cell
    ///
    /// See `MAPPING_FLAG_BYTES_AS_CELL`
    pub bytes_as_cell: bool,

    /// Insert default cell in case of error with `MAPPING_FLAG_BYTES_AS_CELL`
    ///
    /// See `MAPPING_FLAG_IGNORE_INVALID_CELL`
    pub ignore_invalid_cell: bool,
}

impl EthToTonMappingContext {
    pub fn update(&mut self, flags: u8) {
        self.tuples_to_new_cell = flags & MAPPING_FLAG_TUPLES_TO_NEW_CELL != 0;
        self.bytes_as_cell = flags & MAPPING_FLAG_BYTES_AS_CELL != 0;
        self.ignore_invalid_cell = flags & MAPPING_FLAG_IGNORE_INVALID_CELL != 0;
    }
}

pub const MAPPING_FLAG_TUPLES_TO_NEW_CELL: u8 = 0b00000001;
pub const MAPPING_FLAG_BYTES_AS_CELL: u8 = 0b00000010;
pub const MAPPING_FLAG_IGNORE_INVALID_CELL: u8 = 0b00000100;

impl From<u8> for EthToTonMappingContext {
    fn from(flags: u8) -> Self {
        let mut ctx = Self::default();
        ctx.update(flags);
        ctx
    }
}

pub fn map_eth_token_to_ton(
    token: ethabi::Token,
    param: &ethabi::ParamType,
    can_update_ctx: bool,
    ctx: &mut EthToTonMappingContext,
) -> Result<Option<ton_abi::TokenValue>> {
    Ok(Some(match (token, param) {
        (ethabi::Token::FixedBytes(x), ethabi::ParamType::FixedBytes(1)) if can_update_ctx => {
            let flags = *x.get(0).ok_or(AbiMappingError::InvalidMappingFlags)?;
            ctx.update(flags);
            return Ok(None);
        }
        (ethabi::Token::FixedBytes(x), _) => ton_abi::TokenValue::FixedBytes(x.to_vec()),
        (ethabi::Token::Bytes(x), _) => {
            if ctx.bytes_as_cell {
                match ton_types::deserialize_tree_of_cells(&mut std::io::Cursor::new(x)) {
                    Ok(cell) => ton_abi::TokenValue::Cell(cell),
                    Err(_) if ctx.ignore_invalid_cell => {
                        ton_abi::TokenValue::Cell(Default::default())
                    }
                    Err(e) => return Err(e),
                }
            } else {
                ton_abi::TokenValue::Bytes(x)
            }
        }
        (ethabi::Token::Uint(x), &ethabi::ParamType::Uint(size)) => {
            let mut bytes = [0u8; 256 / 8];
            x.to_big_endian(&mut bytes);
            let number = BigUint::from_bytes_be(&bytes);
            ton_abi::TokenValue::Uint(ton_abi::Uint { number, size })
        }
        (ethabi::Token::Int(x), &ethabi::ParamType::Int(size)) => {
            let mut bytes = [0u8; 256 / 8];
            x.to_big_endian(&mut bytes);
            let number = BigInt::from_signed_bytes_be(&bytes);
            ton_abi::TokenValue::Int(ton_abi::Int { number, size })
        }
        (ethabi::Token::Address(ad), _) => ton_abi::TokenValue::Bytes(ad.0.to_vec()),
        (ethabi::Token::String(a), _) => ton_abi::TokenValue::String(a),
        (ethabi::Token::Bool(a), _) => ton_abi::TokenValue::Bool(a),
        (ethabi::Token::FixedArray(a), ethabi::ParamType::FixedArray(abi, _)) => {
            let param_type = match *abi.clone() {
                ethabi::ParamType::Array(arr) => {
                    let mut mapped = map_eth_abi_to_ton(std::iter::once(arr.as_ref()), false)?;
                    anyhow::ensure!(!mapped.is_empty(), "No types");
                    mapped.remove(0)
                }
                _ => anyhow::bail!("Bad abi"),
            };
            ton_abi::TokenValue::FixedArray(
                param_type,
                a.into_iter()
                    .filter_map(|value| map_eth_token_to_ton(value, abi, false, ctx).transpose())
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
        (ethabi::Token::Array(a), ethabi::ParamType::Array(abi)) => {
            let param_type = match *abi.clone() {
                ethabi::ParamType::Array(arr) => {
                    let mut mapped = map_eth_abi_to_ton(std::iter::once(arr.as_ref()), false)?;
                    anyhow::ensure!(!mapped.is_empty(), "No types");
                    mapped.remove(0)
                }
                _ => anyhow::bail!("Bad abi"),
            };
            ton_abi::TokenValue::Array(
                param_type,
                a.into_iter()
                    .filter_map(|value| map_eth_token_to_ton(value, abi, false, ctx).transpose())
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
        (ethabi::Token::Tuple(a), ethabi::ParamType::Tuple(abi)) => {
            // NOTE: save flag before processing tokens to prevent updating
            let to_new_cell = ctx.tuples_to_new_cell;

            let tokens = a
                .into_iter()
                .zip(abi.iter())
                .filter_map(|(value, abi)| {
                    map_eth_token_to_ton(value, abi, can_update_ctx, ctx).transpose()
                })
                .collect::<Result<Vec<_>, _>>()?;

            if to_new_cell {
                ton_abi::TokenValue::Cell(
                    ton_abi::TokenValue::pack_token_values_into_chain(
                        &tokens,
                        Default::default(),
                        ton_abi::contract::ABI_VERSION_2_1,
                    )?
                    .into(),
                )
            } else {
                ton_abi::TokenValue::Tuple(
                    tokens
                        .into_iter()
                        .map(|x| ton_abi::Token::new("", x))
                        .collect(),
                )
            }
        }
        ty => return Err(AbiMappingError::UnsupportedEthType(ty.0).into()),
    }))
}
