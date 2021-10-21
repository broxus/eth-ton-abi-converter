pub use self::eth_to_ton::*;
pub use self::ton_to_eth::*;

mod eth_to_ton;
mod ton_to_eth;

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
