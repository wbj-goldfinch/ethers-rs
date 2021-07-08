use super::base::{decode_function_data, AbiError};
use ethers_core::{
    abi::{Detokenize, Function, InvalidOutputType},
    types::{Address, BlockId, Bytes, TransactionRequest, U256},
};
use ethers_providers::{Middleware, PendingTransaction, ProviderError};

use std::{fmt::Debug, marker::PhantomData, sync::Arc};

use thiserror::Error as ThisError;

#[derive(ThisError, Debug)]
/// An Error which is thrown when interacting with a smart contract
pub enum ContractError<M: Middleware> {
    /// Thrown when the ABI decoding fails
    #[error(transparent)]
    DecodingError(#[from] ethers_core::abi::Error),

    /// Thrown when the internal BaseContract errors
    #[error(transparent)]
    AbiError(#[from] AbiError),

    /// Thrown when detokenizing an argument
    #[error(transparent)]
    DetokenizationError(#[from] InvalidOutputType),

    /// Thrown when a middleware call fails
    #[error("{0}")]
    MiddlewareError(M::Error),

    /// Thrown when a provider call fails
    #[error("{0}")]
    ProviderError(ProviderError),

    /// Thrown during deployment if a constructor argument was passed in the `deploy`
    /// call but a constructor was not present in the ABI
    #[error("constructor is not defined in the ABI")]
    ConstructorError,

    /// Thrown if a contract address is not found in the deployment transaction's
    /// receipt
    #[error("Contract was not deployed")]
    ContractNotDeployed,
}

#[derive(Debug, Clone)]
#[must_use = "contract calls do nothing unless you `send` or `call` them"]
/// Helper for managing a transaction before submitting it to a node
pub struct ContractCall<M, D> {
    /// The raw transaction object
    pub tx: TransactionRequest,
    /// The ABI of the function being called
    pub function: Function,
    /// Optional block number to be used when calculating the transaction's gas and nonce
    pub block: Option<BlockId>,
    pub(crate) client: Arc<M>,
    pub(crate) datatype: PhantomData<D>,
}

impl<M, D: Detokenize> ContractCall<M, D> {
    /// Sets the `from` field in the transaction to the provided value
    pub fn from<T: Into<Address>>(mut self, from: T) -> Self {
        self.tx.from = Some(from.into());
        self
    }

    /// Sets the `gas` field in the transaction to the provided value
    pub fn gas<T: Into<U256>>(mut self, gas: T) -> Self {
        self.tx.gas = Some(gas.into());
        self
    }

    /// Sets the `gas_price` field in the transaction to the provided value
    pub fn gas_price<T: Into<U256>>(mut self, gas_price: T) -> Self {
        self.tx.gas_price = Some(gas_price.into());
        self
    }

    /// Sets the `value` field in the transaction to the provided value
    pub fn value<T: Into<U256>>(mut self, value: T) -> Self {
        self.tx.value = Some(value.into());
        self
    }

    /// Sets the `block` field for sending the tx to the chain
    pub fn block<T: Into<BlockId>>(mut self, block: T) -> Self {
        self.block = Some(block.into());
        self
    }
}

impl<M, D> ContractCall<M, D>
where
    M: Middleware,
    D: Detokenize,
{
    /// Returns the underlying transaction's ABI encoded data
    pub fn calldata(&self) -> Option<Bytes> {
        self.tx.data.clone()
    }

    /// Returns the estimated gas cost for the underlying transaction to be executed
    pub async fn estimate_gas(&self) -> Result<U256, ContractError<M>> {
        self.client
            .estimate_gas(&self.tx)
            .await
            .map_err(ContractError::MiddlewareError)
    }

    /// Queries the blockchain via an `eth_call` for the provided transaction.
    ///
    /// If executed on a non-state mutating smart contract function (i.e. `view`, `pure`)
    /// then it will return the raw data from the chain.
    ///
    /// If executed on a mutating smart contract function, it will do a "dry run" of the call
    /// and return the return type of the transaction without mutating the state
    ///
    /// Note: this function _does not_ send a transaction from your account
    pub async fn call(&self) -> Result<D, ContractError<M>> {
        let bytes = self
            .client
            .call(&self.tx, self.block)
            .await
            .map_err(ContractError::MiddlewareError)?;

        // decode output
        let data = decode_function_data(&self.function, &bytes, false)?;

        Ok(data)
    }

    /// Signs and broadcasts the provided transaction
    pub async fn send(&self) -> Result<PendingTransaction<'_, M::Provider>, ContractError<M>> {
        self.client
            .send_transaction(self.tx.clone(), self.block)
            .await
            .map_err(ContractError::MiddlewareError)
    }
}

#[cfg(test)]
mod tests {
    use crate::BaseContract;
    use ethers_core::abi::Abi;
    use ethers_core::types::U256;

    use super::*;

    #[test]
    fn encodes_abi_v2() {
        // taken from dbg.js
        let expected = "af5e556c07128a7f1ae85cb4496af0da0293cf89ba0a90f253221d888b11d241d1cf60972dbc9b33499677addefeeb4abca51c4eed331eeb7e863b877793ebe5a92967eb1ef9ea2a49cedb5e34284a9c4474d637422fbfd363df7188260f5545aa13ede31f970091dd46eb7252661cf020521ee259de4d6180ec73d85bc7a3abf44734460c401543650fa5dc846c1fad4469f0cbc1b662f66d7f32c7fcd663abd6b19bba1e6572cc4e727576d8c98afb7f9d8e0ea6d7472216fde4f6899bde48126eeae21fb23628d29e6b7dc746141388c627f9e763d41a8b4639f7568338a9e3a7f71b22d96057abae697072c991abd309ae41f2588b9a0df1b864c5eb440a6674672c000000000000000000000000000000000000000000000000000000000000012000000000000000000000000000000000000000000000000000000000000000012100000000000000000000000000000000000000000000000000000000000000";

        let abi = r#"[{"inputs":[{"components":[{"internalType":"uint256","name":"X","type":"uint256"},{"internalType":"uint256","name":"Y","type":"uint256"}],"internalType":"struct Pairing.G1Point","name":"alpha1","type":"tuple"},{"components":[{"internalType":"uint256[2]","name":"X","type":"uint256[2]"},{"internalType":"uint256[2]","name":"Y","type":"uint256[2]"}],"internalType":"struct Pairing.G2Point","name":"beta2","type":"tuple"},{"components":[{"internalType":"uint256[2]","name":"X","type":"uint256[2]"},{"internalType":"uint256[2]","name":"Y","type":"uint256[2]"}],"internalType":"struct Pairing.G2Point","name":"gamma2","type":"tuple"},{"components":[{"internalType":"uint256[2]","name":"X","type":"uint256[2]"},{"internalType":"uint256[2]","name":"Y","type":"uint256[2]"}],"internalType":"struct Pairing.G2Point","name":"delta2","type":"tuple"}],"stateMutability":"nonpayable","type":"constructor"},{"inputs":[{"components":[{"components":[{"internalType":"uint256","name":"X","type":"uint256"},{"internalType":"uint256","name":"Y","type":"uint256"}],"internalType":"struct Pairing.G1Point","name":"A","type":"tuple"},{"components":[{"internalType":"uint256[2]","name":"X","type":"uint256[2]"},{"internalType":"uint256[2]","name":"Y","type":"uint256[2]"}],"internalType":"struct Pairing.G2Point","name":"B","type":"tuple"},{"components":[{"internalType":"uint256","name":"X","type":"uint256"},{"internalType":"uint256","name":"Y","type":"uint256"}],"internalType":"struct Pairing.G1Point","name":"C","type":"tuple"}],"internalType":"struct Verifier.Proof","name":"","type":"tuple"},{"internalType":"uint256[]","name":"","type":"uint256[]"}],"name":"myVerify","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"pure","type":"function"}]"#;

        // g1
        let a = (
            U256::from_dec_str(
                "3198949054991667280165387084635600597227927865026280974964987118907363909783",
            )
            .unwrap(),
            U256::from_dec_str(
                "20687316587816052322568856512175379916584501800508271344391992766752732309483",
            )
            .unwrap(),
        );

        // g2
        let b = (
            [
                U256::from_dec_str(
                    "14010946525363611648783965021539014007086080755179233678304950458716700012003",
                )
                .unwrap(),
                U256::from_dec_str(
                    "14288496145358251946737569813676839799632418165244761628157996564732870865990",
                )
                .unwrap(),
            ],
            [
                U256::from_dec_str(
                    "5540979148777701188106525011422898573472769630054493805938775026195596680122",
                )
                .unwrap(),
                U256::from_dec_str(
                    "13748629318214707079285830103609567267062645952182974563690706202913105963746",
                )
                .unwrap(),
            ],
        );

        // g1
        let c = (
            U256::from_dec_str(
                "14336570878493155239014816646593727250360001480347538979638914553463374870299",
            )
            .unwrap(),
            U256::from_dec_str(
                "15762707596132769298353224166019448246283617917341112120154135659113140741932",
            )
            .unwrap(),
        );

        // f
        let inputs = vec![U256::from_dec_str(
            "14926324003247790816319697286276175621710583960805228958211329188520051867648",
        )
        .unwrap()];

        let proof = (a, b, c);
        let args = (proof, inputs);

        let iface = BaseContract::from(serde_json::from_str::<Abi>(&abi).unwrap());
        let encoded = iface.encode("myVerify", args).unwrap();
        assert_eq!(hex::encode(encoded.as_ref()), expected);
    }
}
