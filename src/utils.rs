use std::convert::TryInto;

use wasm_bindgen::{JsCast, JsValue};

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

pub fn keccak256(bytes: &[u8]) -> [u8; 32] {
    use tiny_keccak::{Hasher, Keccak};
    let mut output = [0u8; 32];
    let mut hasher = Keccak::v256();
    hasher.update(bytes);
    hasher.finalize(&mut output);
    output
}

pub fn compute_eth_address(public_key: &secp256k1::PublicKey) -> [u8; 20] {
    let pub_key = &public_key.serialize_uncompressed()[1..];
    keccak256(pub_key)[32 - 20..].try_into().unwrap()
}

#[derive(thiserror::Error, Debug)]
pub enum AbiMappingError {
    #[error("Unsupported type: {:?}", .0)]
    UnsupportedTonType(ton_abi::TokenValue),
    #[error("Unsupported type: {:?}", .0)]
    UnsupportedEthType(ethabi::Token),
    #[error("Invalid mapping flags")]
    InvalidMappingFlags,
    #[error("Incomplete deserialization")]
    IncompleteDeserialization,
}
