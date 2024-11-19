//! Minimal repro that shows why implementing cheatcodes with `EvmWiring` is hard without changes to Foundry or REVM.
//! In general, the code is quite complex and there seems to be one blocker in the `DatabaseExt::method_that_constructs_inspector` that I haven't found a workaround for yet.
use revm::precompile::{Address, B256};
use revm::state::AccountInfo;
use revm::{
    database_interface::EmptyDB,
    specification::hardfork::SpecId,
    wiring::{
        default::{block::BlockEnv, Env, TxEnv},
        result::{EVMError, InvalidTransaction, ResultAndState},
    },
    Database, Evm, EvmWiring, InnerEvmContext,
};
use revm_bytecode::Bytecode;
use revm_inspector::inspectors::NoOpInspector;
use revm_inspector::{inspector_handle_register, Inspector};
use revm_primitives::U256;
use revm_wiring::result::HaltReason;
use revm_wiring::{EthereumWiring, EvmWiring as EvmWiringTypes, TransactionValidation};
use std::convert::Infallible;
use std::fmt::Debug;

/// Ethereum L1 backend for cheatcodes.
#[derive(Clone, Debug, Default)]
struct Backend {
    db: EmptyDB,
    env: Box<Env<BlockEnv, TxEnv>>,
    spec_id: SpecId,
}

impl Database for Backend {
    type Error = Infallible;

    fn basic(&mut self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        self.db.basic(address)
    }

    fn code_by_hash(&mut self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        self.db.code_by_hash(code_hash)
    }

    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Self::Error> {
        self.db.storage(address, index)
    }

    fn block_hash(&mut self, number: u64) -> Result<B256, Self::Error> {
        self.db.block_hash(number)
    }
}

/// Used in Foundry to implement cheatcodes.
/// See the `Cheatcode` trait below why it needs to take `EvmWiring` as a generic parameter.
trait DatabaseExt<EvmWiringT>: Database<Error = Infallible>
where
    EvmWiringT: EvmWiring,
    EvmWiringT::ExternalContext: Inspector<EvmWiringT> + Debug,
{
    fn method_that_takes_inspector_as_argument(self, inspector: EvmWiringT::ExternalContext);
    fn method_that_constructs_inspector(self);
}

// We need to set the associated types to specific ones to make `method_that_takes_inspector_as_argument` work if the backend is not generic.
impl<
        EvmWiringT: EvmWiring<Database = Backend, Block = BlockEnv, Transaction = TxEnv, Hardfork = SpecId>,
    > DatabaseExt<EvmWiringT> for Backend
where
    EvmWiringT::ExternalContext: Inspector<EvmWiringT> + Debug,
{
    fn method_that_takes_inspector_as_argument(self, inspector: EvmWiringT::ExternalContext) {
        let spec_id = self.spec_id;
        let env = self.env.clone();
        inspect_wiring::<'_, EvmWiringT>(self, env, spec_id, inspector).unwrap();
    }

    fn method_that_constructs_inspector(self) {
        let spec_id = self.spec_id;
        let env = self.env.clone();
        let inspector = NoOpInspector;
        // Problem: the following line won't compile with "expected associated type, found `NoOpInspector`" error.
        // inspect_wiring::<'_, EvmWiringT>(self, env, spec_id, inspector).unwrap();
        // As a workaround we can use a helper method that is only generic in the inspector. But this won't work if we want to make `Backend` generic.
        inspect_backend(self, env, spec_id, inspector).unwrap();
    }
}

/// Generic function to execute a transaction without committing it and runs the inspector.
fn inspect_wiring<'a, EvmWiringT>(
    db: EvmWiringT::Database,
    env: Box<
        Env<<EvmWiringT as EvmWiringTypes>::Block, <EvmWiringT as EvmWiringTypes>::Transaction>,
    >,
    spec_id: EvmWiringT::Hardfork,
    inspector: EvmWiringT::ExternalContext,
) -> Result<
    (
        ResultAndState<EvmWiringT::HaltReason>,
        Box<Env<EvmWiringT::Block, EvmWiringT::Transaction>>,
    ),
    EVMError<
        <<EvmWiringT as EvmWiringTypes>::Database as Database>::Error,
        <<EvmWiringT as EvmWiringTypes>::Transaction as TransactionValidation>::ValidationError,
    >,
>
where
    EvmWiringT: EvmWiring + 'a,
    <EvmWiringT as EvmWiringTypes>::Transaction: Default,
    <<EvmWiringT as EvmWiringTypes>::Transaction as TransactionValidation>::ValidationError:
        From<InvalidTransaction>,
    <EvmWiringT as EvmWiringTypes>::Block: Default,
    <EvmWiringT as EvmWiringTypes>::ExternalContext: Inspector<EvmWiringT>,
{
    let mut evm = Evm::<'a, EvmWiringT>::builder()
        .with_db(db)
        .with_env(env)
        .with_spec_id(spec_id)
        .with_external_context(inspector)
        .append_handler_register(inspector_handle_register)
        .build();
    let res = evm.transact()?;
    let (_, env, _) = evm.into_db_and_env_with_handler_cfg();
    Ok((res, env))
}

/// Function to execute a transaction without committing it and runs the inspector.
/// Only generic in the inspector, not in the wiring.
fn inspect_backend<InspectorT>(
    db: Backend,
    env: Box<Env<BlockEnv, TxEnv>>,
    spec_id: SpecId,
    inspector: InspectorT,
) -> Result<
    (ResultAndState<HaltReason>, Box<Env<BlockEnv, TxEnv>>),
    EVMError<Infallible, InvalidTransaction>,
>
where
    InspectorT: Inspector<EthereumWiring<Backend, InspectorT>> + Debug,
{
    let mut evm = revm::Evm::<'_, EthereumWiring<Backend, InspectorT>>::builder()
        .with_db(db)
        .with_env(env)
        .with_spec_id(spec_id)
        .with_external_context(inspector)
        .append_handler_register(inspector_handle_register)
        .build();
    let res = evm.transact()?;
    let (_, env, _) = evm.into_db_and_env_with_handler_cfg();
    Ok((res, env))
}

struct CheatsCtxt<EvmWiringT: EvmWiring> {
    ecx: InnerEvmContext<EvmWiringT>,
}

trait Cheatcode {
    /// The cheatcode inspector gets access to `Backend` abstracted by the `DatabaseExt` trait through `InnerEvmContext` from `CheatsCtxt`.
    /// There is a method in `DatabaseExt` that takes a generic inspector as argument (this could be potentially made non-generic to simplify things).
    /// But the `Inspector` trait takes a generic `EvmWiring` as type parameter.
    /// We need to make sure the two match, so we need `DatabaseExt` to take an `EvmWiring` type parameter as well.
    fn apply_stateful<EvmWiringT: EvmWiring>(&self, ccx: &mut CheatsCtxt<EvmWiringT>)
    where
        EvmWiringT::Database: DatabaseExt<EvmWiringT>,
        <EvmWiringT as revm_wiring::EvmWiring>::ExternalContext: Inspector<EvmWiringT> + Debug;
}

#[cfg(test)]
mod tests {
    use super::*;
    use revm_inspector::inspectors::NoOpInspector;

    #[test]
    fn method_that_takes_inspector_as_argument() {
        let backend = Backend::default();
        <Backend as DatabaseExt<EthereumWiring<Backend, NoOpInspector>>>::method_that_takes_inspector_as_argument(
            backend,
            NoOpInspector,
        );
    }

    #[test]
    fn method_that_constructs_inspector() {
        let backend = Backend::default();
        <Backend as DatabaseExt<EthereumWiring<Backend, NoOpInspector>>>::method_that_constructs_inspector(
            backend,
        );
    }
}
