#![allow(clippy::unused_unit)]

use std::str::FromStr;
use ton_types::SliceData;
use wasm_bindgen::prelude::*;
use wasm_bindgen::{JsCast, JsValue};

use ::eth_ton_abi_converter::*;

#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[wasm_bindgen(js_name = "mapTonCellIntoSolBytes")]
pub fn map_ton_cell_into_sol_bytes(abi: &str, boc: &str) -> Result<String, JsValue> {
    // Parse ABI
    let params = decode_ton_event_abi(abi).handle_error()?;

    // Parse BOC
    let boc = base64::decode(boc).handle_error()?;
    let cell = ton_types::deserialize_tree_of_cells(&mut boc.as_slice()).handle_error()?;

    // Unpack tokens
    let tokens = unpack_from_cell(&params, SliceData::load_cell(cell).handle_error()?).handle_error()?;

    // Serialize tokens
    borsh::serialize(&tokens).map(base64::encode).handle_error()
}

#[wasm_bindgen(js_name = "mapSolBytesIntoTonCell")]
pub fn map_sol_bytes_into_ton_cell(abi: &str, data: &str) -> Result<String, JsValue> {
    // Parse ABI
    let params = decode_ton_event_abi(abi).handle_error()?;

    // Parse tokens
    let bytes = base64::decode(data).handle_error()?;
    let tokens = borsh::deserialize(&mut bytes.as_slice(), &params).handle_error()?;

    // Pack tokens
    let cells = Vec::with_capacity(tokens.len());
    let cell = ton_abi::TokenValue::pack_values_into_chain(
        &tokens,
        cells,
        &ton_abi::contract::ABI_VERSION_2_2,
    )
    .and_then(|builder| builder.into_cell())
    .handle_error()?;
    ton_types::serialize_toc(&cell)
        .handle_error()
        .map(base64::encode)
}

#[wasm_bindgen(js_name = "mapTonCellIntoEthBytes")]
pub fn map_ton_cell_into_eth_bytes(abi: &str, boc: &str, flags: &str) -> Result<String, JsValue> {
    let flags = flags.trim();

    // Unused by now, reserved
    let _flags = match flags.strip_prefix("0x") {
        Some(flags) => u64::from_str_radix(flags, 16),
        None => u64::from_str(flags),
    }
    .handle_error()?;

    // Parse ABI
    let params = decode_ton_event_abi(abi).handle_error()?;

    // Parse BOC
    let boc = base64::decode(boc).handle_error()?;
    let cell = ton_types::deserialize_tree_of_cells(&mut boc.as_slice()).handle_error()?;

    // Unpack tokens
    let tokens = unpack_from_cell(&params, SliceData::load_cell(cell).handle_error()?).handle_error()?;

    // Map tokens
    map_ton_tokens_to_eth_bytes(tokens)
        .handle_error()
        .map(hex::encode)
        .map(|bytes| format!("0x{}", bytes))
}

#[wasm_bindgen(js_name = "mapEthBytesIntoTonCell")]
pub fn map_eth_bytes_into_ton_cell(abi: &str, data: &str, flags: &str) -> Result<String, JsValue> {
    let flags = flags.trim();
    let flags = match flags.strip_prefix("0x") {
        Some(flags) => u64::from_str_radix(flags, 16),
        None => u64::from_str(flags),
    }
    .handle_error()?;
    let ctx = EthToTonMappingContext::from(flags as u8);

    // Parse ABI
    let event = decode_eth_event_abi(abi).handle_error()?;
    let params = event
        .inputs
        .iter()
        .map(|item| item.kind.clone())
        .collect::<Vec<_>>();

    // Parse data
    let data = hex::decode(data.strip_prefix("0x").unwrap_or(data)).handle_error()?;
    let tokens = ethabi::decode(&params, &data).handle_error()?;

    // Map tokens
    let cell = map_eth_tokens_to_ton_cell(tokens, &params, ctx).handle_error()?;
    ton_types::serialize_toc(&cell)
        .handle_error()
        .map(base64::encode)
}

impl<T, E> HandleError for Result<T, E>
where
    E: ToString,
{
    type Output = T;

    fn handle_error(self) -> Result<Self::Output, JsValue> {
        self.map_err(|e| {
            let error = e.to_string();
            js_sys::Error::new(&error).unchecked_into()
        })
    }
}

pub trait HandleError {
    type Output;

    fn handle_error(self) -> Result<Self::Output, JsValue>;
}
