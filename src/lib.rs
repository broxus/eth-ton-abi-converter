use wasm_bindgen::prelude::*;

use crate::eth_to_ton::*;
use crate::ton_to_eth::*;
use crate::utils::*;

mod eth_to_ton;
mod ton_to_eth;
mod utils;

#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[wasm_bindgen(js_name = "mapTonCellIntoEthBytes")]
pub fn map_ton_cell_into_eth_bytes(abi: &str, boc: &str) -> Result<String, JsValue> {
    // Parse ABI
    let params = decode_ton_event_abi(abi).handle_error()?;

    // Parse boc
    let boc = base64::decode(boc).handle_error()?;
    let cell =
        ton_types::deserialize_tree_of_cells(&mut std::io::Cursor::new(&boc)).handle_error()?;

    // Unpack tokens
    let tokens = unpack_from_cell(&params, cell.into()).handle_error()?;

    // Map tokens
    map_ton_tokens_to_eth_bytes(tokens)
        .handle_error()
        .map(hex::encode)
        .map(|bytes| format!("0x{}", bytes))
}

#[wasm_bindgen(js_name = "mapEthBytesIntoTonCell")]
pub fn map_eth_bytes_into_ton_cell(abi: &str, data: &str) -> Result<String, JsValue> {
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
    let cell = map_eth_tokens_to_ton_cell(tokens, &params).handle_error()?;
    ton_types::serialize_toc(&cell)
        .handle_error()
        .map(base64::encode)
}
