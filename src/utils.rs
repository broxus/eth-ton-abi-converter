use wasm_bindgen::JsCast;
use wasm_bindgen::JsValue;

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
