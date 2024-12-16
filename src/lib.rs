//! Experiments with multichain REVM for Foundry-style Solidity test cheatcodes to provide feedback on the REVM
//! implementation.
//!
//! The design of the REVM implementation seems sound, but there are some issues that came up during the experiment that
//! are blockers for a multichain Solidity test implementation.
//!
//! Discovered issues:
//! - Can't get precompiles in `Inspector::Call`. Previously this was accessed via `EvmContext::precompiles`.
//! - `Evm::transact()` implementation hard-codes mainnet `HaltReason`.
//! - `InspectorCtx for InspectorContext` implementation hard-codes mainnet `EthInterpreter`.
//! - When using a generic `PrecompileProvider` along with an `Inspector`, the `PrecompileProvider` needs the
//!   `InspectorContext` as the context instead of `Inspector::Context`. See
//!   `DatabaseExt::method_that_constructs_inspector` for a concrete issue.
//! - `NoOpInspector::default()` doesn't work with mainnet types due to unsatisfied trait bounds.
//!
//! Learnings:
//! - The `Database` lifetimes are difficult in inspectors with the introduction of the generic context. There is one
//!   outstanding TODO in `Cheatcodes::apply_cheatcode` that I haven't figured out yet, but it's probably solvable.
//! - Compiler errors are not great. It's difficult to pinpoint the source of the error, and if the compiler makes a
//!   suggestion how to fix it, it's usually wrong.
use std::{convert::Infallible, fmt::Debug};

use revm::{
    context::{BlockEnv, Cfg, CfgEnv, TxEnv},
    context_interface::{
        result::{EVMError, HaltReason, InvalidTransaction, ResultAndState},
        Block, Transaction,
    },
    database_interface::EmptyDB,
    handler::EthPrecompileProvider,
    handler_interface::PrecompileProvider,
    precompile::{Address, B256},
    state::AccountInfo,
    Context, Database, Evm,
};
use revm_bytecode::Bytecode;
use revm_inspector::{
    inspector_handler, inspectors::GasInspector, GetInspector, Inspector, InspectorContext, InspectorHandler,
};
use revm_interpreter::{interpreter::EthInterpreter, CallInputs, CallOutcome};
use revm_primitives::U256;

/// Backend for cheatcodes.
#[derive(Clone, Debug, Default)]
pub struct Backend {
    db: EmptyDB,
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

/// Used in Foundry to provide extended functionality to cheatcodes from inspectors.
pub trait DatabaseExt: Database<Error = Infallible> {
    /// Mimics `DatabaseExt::transact`
    /// See `inspect_backend` for the generics
    fn method_that_takes_inspector_as_argument<'backend, InspectorT, BlockT, TxT, CfgT, PrecompileT>(
        &'backend mut self,
        env: Env<BlockT, TxT, CfgT>,
        inspector: InspectorT,
    ) where
        InspectorT: Inspector<Context = Context<BlockT, TxT, CfgT, &'backend mut Backend>, InterpreterTypes = EthInterpreter>
            + GetInspector<Inspector = InspectorT>,
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
            Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        >;

    /// Mimics `DatabaseExt::roll_fork_to_transaction`
    fn method_that_constructs_inspector<BlockT, TxT, CfgT /* PrecompileT */>(&mut self, env: Env<BlockT, TxT, CfgT>)
    where
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg;
    // Can't declare a method that takes the provider as a generic parameter and constructs a
    // new inspector, because the `PrecompileProvider` trait needs to know the inspector type
    // due to its context being `InspectorContext` instead of `Context`.
    // `DatabaseExt::roll_fork_to_transaction` actually creates a noop inspector, so it not working is not a hard
    // blocker for multichain cheatcodes.
    /*
    PrecompileT: PrecompileProvider<
        Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
        Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
    >
    */
}

impl DatabaseExt for Backend {
    fn method_that_takes_inspector_as_argument<'backend, InspectorT, BlockT, TxT, CfgT, PrecompileT>(
        &'backend mut self,
        env: Env<BlockT, TxT, CfgT>,
        inspector: InspectorT,
    ) where
        InspectorT: Inspector<Context = Context<BlockT, TxT, CfgT, &'backend mut Backend>, InterpreterTypes = EthInterpreter>
            + GetInspector<Inspector = InspectorT>,
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
            Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        >,
    {
        inspect_backend::<InspectorT, BlockT, TxT, CfgT, PrecompileT>(self, env, inspector).unwrap();
    }

    fn method_that_constructs_inspector<'backend, BlockT, TxT, CfgT /* , PrecompileT */>(
        &'backend mut self,
        env: Env<BlockT, TxT, CfgT>,
    ) where
        /*InspectorT: Inspector<
            Context = Context<BlockT, TxT, CfgT, &'backend mut Backend>,
            InterpreterTypes = EthInterpreter,
        > + GetInspector<Inspector = InspectorT>,*/
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        /*PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
            Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        >,*/
    {
        // Since we can't have a generic precompiles type param as explained in the trait definition, we're using a
        // concrete type here.
        inspect_backend_with_eth_precompile::<
            GasInspector<Context<BlockT, TxT, CfgT, &'backend mut Backend>, EthInterpreter>,
            BlockT,
            TxT,
            CfgT,
        >(self, env, GasInspector::new())
        .unwrap();
    }
}

/// An REVM inspector that intercepts calls the cheatcode address and executes them with the help of the `DatabaseExt`
/// trait.
#[derive(Clone, Default)]
pub struct Cheatcodes<'backend, BlockT, TxT, CfgT> {
    phantom: core::marker::PhantomData<(&'backend mut Backend, BlockT, TxT, CfgT)>,
}

impl<'backend, BlockT, TxT, CfgT> Cheatcodes<'backend, BlockT, TxT, CfgT>
where
    BlockT: Block + Clone,
    TxT: Transaction + Clone,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg + Clone,
{
    fn apply_cheatcode(&mut self, context: &mut Context<BlockT, TxT, CfgT, &'backend mut Backend>) {
        // `rollFork(bytes32 transaction)` cheatcode would do this
        context.journaled_state.database.method_that_constructs_inspector(Env {
            block: context.block.clone(),
            tx: context.tx.clone(),
            cfg: context.cfg.clone(),
        });

        // `transact` cheatcode would do this
        // This is a "recursive" call where we launch a new transaction using the same inspector.
        // TODO figure out how to express the self lifetime here
        // context
        //     .journaled_state
        //     .database
        //     .method_that_takes_inspector_as_argument::<'backend, &mut Self, BlockT, TxT, CfgT,
        //         EthPrecompileProvider<
        //             InspectorContext<&mut Self, BlockT, TxT, CfgT, &'backend mut Backend>,
        //             EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        //         >>(
        //         Env {
        //             block: context.block.clone(),
        //             tx: context.tx.clone(),
        //             cfg: context.cfg.clone(),
        //         },
        //         self,
        //     );
    }
}

impl<'backend, BlockT, TxT, CfgT> Inspector for Cheatcodes<'backend, BlockT, TxT, CfgT>
where
    BlockT: Block + Clone,
    TxT: Transaction + Clone,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg + Clone,
{
    type Context = Context<BlockT, TxT, CfgT, &'backend mut Backend>;
    type InterpreterTypes = EthInterpreter;

    // TODO: how to get precompiles? Previously this was accessed via `EvmContext::precompiles`.
    fn call(&mut self, context: &mut Self::Context, _inputs: &mut CallInputs) -> Option<CallOutcome> {
        self.apply_cheatcode(context);
        None
    }
}

/// EVM environment
#[derive(Clone, Debug)]
pub struct Env<BlockT, TxT, CfgT> {
    pub block: BlockT,
    pub tx: TxT,
    pub cfg: CfgT,
}

impl Env<BlockEnv, TxEnv, CfgEnv> {
    pub fn mainnet() -> Self {
        Self {
            block: BlockEnv::default(),
            tx: TxEnv::default(),
            cfg: CfgEnv::default(),
        }
    }
}

/// Executes a transaction without committing it and runs the inspector using the `Backend` as the database.
pub fn inspect_backend<'backend, InspectorT, BlockT, TxT, CfgT, PrecompileT>(
    backend: &'backend mut Backend,
    env: Env<BlockT, TxT, CfgT>,
    inspector: InspectorT,
) -> Result<
    // Generic halt reason is not supported yet in the `Evm` implementation
    ResultAndState<HaltReason>,
    EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
>
where
    InspectorT: Inspector<
            // Explicit lifetime needed for `&mut Backend`
            Context = Context<BlockT, TxT, CfgT, &'backend mut Backend>,
            // Generic interpreter types are not supported yet in the `Evm` implementation
            InterpreterTypes = EthInterpreter,
        > + GetInspector<Inspector = InspectorT>,
    BlockT: Block,
    TxT: Transaction,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg,
    PrecompileT: PrecompileProvider<
        Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
        Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
    >,
{
    let context = Context::builder()
        .with_cfg(env.cfg)
        .with_block(env.block)
        .with_tx(env.tx)
        .with_db(backend);
    let inspector_context =
        InspectorContext::<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>::new(context, inspector);

    let handler = inspector_handler::<
        InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
        EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        PrecompileT,
    >();

    let mut evm = Evm::<
        EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
        InspectorHandler<
            InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
            EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
            PrecompileT,
        >,
    >::new(inspector_context, handler);

    evm.transact()
}

/// Executes a transaction without committing it and runs the inspector using the `Backend` as the
/// database and the `EthPrecompileProvider` as the precompiles.
pub fn inspect_backend_with_eth_precompile<'backend, InspectorT, BlockT, TxT, CfgT>(
    backend: &'backend mut Backend,
    env: Env<BlockT, TxT, CfgT>,
    inspector: InspectorT,
) -> Result<
    // Generic halt reason is not supported yet in the `Evm` implementation
    ResultAndState<HaltReason>,
    EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
>
where
    InspectorT: Inspector<
            // Explicit lifetime needed for `&mut Backend`
            Context = Context<BlockT, TxT, CfgT, &'backend mut Backend>,
            // Generic interpreter types are not supported yet in the `Evm` implementation
            InterpreterTypes = EthInterpreter,
        > + GetInspector<Inspector = InspectorT>,
    BlockT: Block,
    TxT: Transaction,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg,
{
    let context = Context::builder()
        .with_cfg(env.cfg)
        .with_block(env.block)
        .with_tx(env.tx)
        .with_db(backend);
    let inspector_context =
        InspectorContext::<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>::new(context, inspector);

    let handler = inspector_handler::<
        InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
        EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        EthPrecompileProvider<
            InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
            EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        >,
    >();

    let mut evm = Evm::<
        EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
        InspectorHandler<
            InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
            EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
            EthPrecompileProvider<
                InspectorContext<InspectorT, BlockT, TxT, CfgT, &'backend mut Backend>,
                EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
            >,
        >,
    >::new(inspector_context, handler);

    evm.transact()
}

#[cfg(test)]
mod tests {
    use revm::EthContext;

    use super::*;

    #[test]
    fn method_that_takes_inspector_as_argument() {
        let mut backend = Backend::default();

        type ContextT<'backend> = EthContext<&'backend mut Backend>;
        type InspectorT<'backend> = GasInspector<ContextT<'backend>, EthInterpreter>;
        type InspectorContextT<'backend> =
            InspectorContext<InspectorT<'backend>, BlockEnv, TxEnv, CfgEnv, &'backend mut Backend>;
        type ErrorT<'backend> =
            EVMError<<&'backend mut Backend as Database>::Error, <TxEnv as Transaction>::TransactionError>;

        backend
            .method_that_takes_inspector_as_argument::<_, _, _, _, EthPrecompileProvider<InspectorContextT, ErrorT>>(
                Env::mainnet(),
                InspectorT::new(),
            );
    }

    #[test]
    fn method_that_constructs_inspector() {
        let mut backend = Backend::default();
        backend.method_that_constructs_inspector(Env::mainnet());
    }

    #[test]
    fn inspect_cheatcodes() {
        let mut backend = Backend::default();
        let mut cheatcodes = Cheatcodes::default();

        type InspectorT<'backend, 'cheatcodes> = &'cheatcodes mut Cheatcodes<'backend, BlockEnv, TxEnv, CfgEnv>;
        type ErrorT<'backend> =
            EVMError<<&'backend mut Backend as Database>::Error, <TxEnv as Transaction>::TransactionError>;
        type InspectorContextT<'backend, 'cheatcodes> =
            InspectorContext<InspectorT<'backend, 'cheatcodes>, BlockEnv, TxEnv, CfgEnv, &'backend mut Backend>;

        inspect_backend::<'_, _, _, _, _, EthPrecompileProvider<InspectorContextT, ErrorT>>(
            &mut backend,
            Env::mainnet(),
            &mut cheatcodes,
        )
        .unwrap();
    }
}
