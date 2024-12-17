//! Experiments with multichain REVM for Foundry-style Solidity test cheatcodes to provide feedback on the REVM
//! implementation.
//!
//! The code below mimics relevant parts of the implementation of the [`transact`](https://book.getfoundry.sh/cheatcodes/transact)
//! and [`rollFork(uint256 forkId, bytes32 transaction)`](https://book.getfoundry.sh/cheatcodes/roll-fork#rollfork)
//! cheatcodes that proved difficult to implement with the new interface.
//! Both of these cheatcodes initiate transactions from a call step in the cheatcode inspector.
use std::{convert::Infallible, fmt::Debug};

use revm::{
    context::{BlockEnv, Cfg, CfgEnv, TxEnv},
    context_interface::{
        result::{EVMError, InvalidTransaction},
        Block, Transaction,
    },
    handler::EthPrecompileProvider,
    handler_interface::PrecompileProvider,
    precompile::{Address, B256},
    state::{Account, AccountInfo, EvmState},
    Context, Database, DatabaseCommit, Evm, JournaledState,
};
use revm_bytecode::Bytecode;
use revm_database::InMemoryDB;
use revm_inspector::{
    inspector_handler, inspectors::GasInspector, GetInspector, Inspector, InspectorContext, InspectorHandler,
};
use revm_interpreter::{interpreter::EthInterpreter, CallInputs, CallOutcome};
use revm_primitives::{HashMap, U256};

/// Backend for cheatcodes.
/// The problematic cheatcodes are only supported in fork mode, so we'll omit the non-fork behavior of the `Backend`.
#[derive(Clone, Debug, Default)]
pub struct Backend {
    /// In fork mode, Foundry stores (`JournaledState`, `Database`) pairs for each fork.
    /// We just store the `Database` here for simplicity.
    db: InMemoryDB,
    /// Counters to be able to assert that we mutated the object that we expected to mutate.
    method_with_inspector_counter: usize,
    method_without_inspector_counter: usize,
}

impl Backend {
    pub fn new(db: InMemoryDB) -> Self {
        Self {
            db,
            method_with_inspector_counter: 0,
            method_without_inspector_counter: 0,
        }
    }
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

impl DatabaseCommit for Backend {
    fn commit(&mut self, changes: HashMap<Address, Account>) {
        self.db.commit(changes);
    }
}

/// Used in Foundry to provide extended functionality to cheatcodes.
/// The methods are called from the `Cheatcodes` inspector.
pub trait DatabaseExt: Database<Error = Infallible> {
    /// Mimics `DatabaseExt::transact`
    /// See `commit_transaction` for the generics
    fn method_that_takes_inspector_as_argument<InspectorT, BlockT, TxT, CfgT, PrecompileT>(
        &mut self,
        journaled_state: &mut JournaledState<Backend>,
        env: Env<BlockT, TxT, CfgT>,
        inspector: InspectorT,
    ) where
        InspectorT: Inspector<Context = Context<BlockT, TxT, CfgT, Backend>, InterpreterTypes = EthInterpreter>
            + GetInspector<Inspector = InspectorT>,
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
            Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        >;

    /// Mimics `DatabaseExt::roll_fork_to_transaction`
    fn method_that_constructs_inspector<BlockT, TxT, CfgT /* PrecompileT */>(
        &mut self,
        journaled_state: &mut JournaledState<Backend>,
        env: Env<BlockT, TxT, CfgT>,
    ) where
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg;
    // Can't declare a method that takes the precompile provider as a generic parameter and constructs a
    // new inspector, because the `PrecompileProvider` trait needs to know the inspector type
    // due to its context being `InspectorContext` instead of `Context`.
    // `DatabaseExt::roll_fork_to_transaction` actually creates a noop inspector, so this not working is not a hard
    // blocker for multichain cheatcodes.
    /*
    PrecompileT: PrecompileProvider<
        Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
        Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
    >
    */
}

impl DatabaseExt for Backend {
    fn method_that_takes_inspector_as_argument<InspectorT, BlockT, TxT, CfgT, PrecompileT>(
        &mut self,
        journaled_state: &mut JournaledState<Backend>,
        env: Env<BlockT, TxT, CfgT>,
        inspector: InspectorT,
    ) where
        InspectorT: Inspector<Context = Context<BlockT, TxT, CfgT, Backend>, InterpreterTypes = EthInterpreter>
            + GetInspector<Inspector = InspectorT>,
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
            Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        >,
    {
        commit_transaction::<InspectorT, BlockT, TxT, CfgT, PrecompileT>(journaled_state, env, inspector).unwrap();
        self.method_with_inspector_counter += 1;
    }

    fn method_that_constructs_inspector<BlockT, TxT, CfgT /* , PrecompileT */>(
        &mut self,
        journaled_state: &mut JournaledState<Backend>,
        env: Env<BlockT, TxT, CfgT>,
    ) where
        /*InspectorT: Inspector<
            Context = Context<BlockT, TxT, CfgT, Backend>,
            InterpreterTypes = EthInterpreter,
        > + GetInspector<Inspector = InspectorT>,*/
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        /*PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
            Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        >,*/
    {
        let inspector = GasInspector::new();
        commit_transaction::<
            // Generic interpreter types are not supported yet in the `Evm` implementation
            GasInspector<Context<BlockT, TxT, CfgT, Backend>, EthInterpreter>,
            BlockT,
            TxT,
            CfgT,
            // Since we can't have a generic precompiles type param as explained in the trait definition, we're using a
            // concrete type here.
            EthPrecompileProvider<
                InspectorContext<
                    GasInspector<Context<BlockT, TxT, CfgT, Backend>, EthInterpreter>,
                    BlockT,
                    TxT,
                    CfgT,
                    Backend,
                >,
                EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
            >,
        >(journaled_state, env, inspector)
        .unwrap();

        self.method_without_inspector_counter += 1;
    }
}

/// An REVM inspector that intercepts calls to the cheatcode address and executes them with the help of the
/// `DatabaseExt` trait.
#[derive(Clone, Default)]
pub struct Cheatcodes<BlockT, TxT, CfgT> {
    call_count: usize,
    phantom: core::marker::PhantomData<(Backend, BlockT, TxT, CfgT)>,
}

impl<BlockT, TxT, CfgT> Cheatcodes<BlockT, TxT, CfgT>
where
    BlockT: Block + Clone,
    TxT: Transaction + Clone,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg + Clone,
{
    fn apply_cheatcode(&mut self, context: &mut Context<BlockT, TxT, CfgT, Backend>) {
        // The problematic cheatcodes do recursive calls where we launch a new transaction using the same inspector.
        // They don't work properly due to two mutable borrows of `context.journaled_state` which we work around by
        // cloning the `Backend` to make the calls. But this makes the code incorrect, because `DatabaseExt` methods
        // mutate the cloned object instead of the original `Backend`. With the current released version of REVM
        // cloning is not necessary, because the DB is a sibling of the journaled state, not a child so both can be
        // mutably borrowed at the same time.

        // `transact` cheatcode would do this
        context
            .journaled_state
            .database
            // TODO this clone causes test failure
            .clone()
            .method_that_takes_inspector_as_argument::<&mut Self, BlockT, TxT, CfgT, EthPrecompileProvider<
                InspectorContext<&mut Self, BlockT, TxT, CfgT, Backend>,
                EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
            >>(
                &mut context.journaled_state,
                Env {
                    block: context.block.clone(),
                    tx: context.tx.clone(),
                    cfg: context.cfg.clone(),
                },
                self,
            );

        // `rollFork(bytes32 transaction)` cheatcode would do this
        context
            .journaled_state
            .database
            // TODO this clone causes test failure
            .clone()
            .method_that_constructs_inspector(
                &mut context.journaled_state,
                Env {
                    block: context.block.clone(),
                    tx: context.tx.clone(),
                    cfg: context.cfg.clone(),
                },
            );
    }
}

impl<BlockT, TxT, CfgT> Inspector for Cheatcodes<BlockT, TxT, CfgT>
where
    BlockT: Block + Clone,
    TxT: Transaction + Clone,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg + Clone,
{
    type Context = Context<BlockT, TxT, CfgT, Backend>;
    type InterpreterTypes = EthInterpreter;

    /// Note that precompiles are no longer accessible via `EvmContext::precompiles`.
    fn call(&mut self, context: &mut Self::Context, _inputs: &mut CallInputs) -> Option<CallOutcome> {
        self.call_count += 1;
        // Don't apply cheatcodes recursively.
        if self.call_count == 1 {
            self.apply_cheatcode(context);
        }
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
        // `CfgEnv` is non-exhaustive, so we need to set the field after construction.
        let mut cfg = CfgEnv::default();
        cfg.disable_nonce_check = true;

        Self {
            block: BlockEnv::default(),
            tx: TxEnv::default(),
            cfg,
        }
    }
}

/// Executes a transaction and runs the inspector using the `Backend` as the database.
/// Mimics `commit_transaction` https://github.com/foundry-rs/foundry/blob/25cc1ac68b5f6977f23d713c01ec455ad7f03d21/crates/evm/core/src/backend/mod.rs#L1931
pub fn commit_transaction<InspectorT, BlockT, TxT, CfgT, PrecompileT>(
    journaled_state: &mut JournaledState<Backend>,
    env: Env<BlockT, TxT, CfgT>,
    inspector: InspectorT,
) -> Result<(), EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>>
where
    InspectorT: Inspector<
            Context = Context<BlockT, TxT, CfgT, Backend>,
            // Generic interpreter types are not supported yet in the `Evm` implementation
            InterpreterTypes = EthInterpreter,
        > + GetInspector<Inspector = InspectorT>,
    BlockT: Block,
    TxT: Transaction,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg,
    PrecompileT: PrecompileProvider<
        Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
        Error = EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
    >,
{
    // Create new journaled state and backend with the same DB and journaled state as the original for the transaction.
    // This new backend and state will be discarded after the transaction is done and the changes are applied to the
    // original backend.
    // Mimics https://github.com/foundry-rs/foundry/blob/25cc1ac68b5f6977f23d713c01ec455ad7f03d21/crates/evm/core/src/backend/mod.rs#L1950-L1953
    let new_db = journaled_state.database.db.clone();
    let new_backend = Backend::new(new_db);
    let mut new_journaled_state = JournaledState::new(journaled_state.spec, new_backend);
    let &mut JournaledState {
        database: _,
        ref mut state,
        ref mut transient_storage,
        ref mut logs,
        ref mut depth,
        ref mut journal,
        ref mut spec,
        ref mut warm_preloaded_addresses,
    } = journaled_state;
    new_journaled_state.state = state.clone();
    new_journaled_state.transient_storage = transient_storage.clone();
    new_journaled_state.logs = logs.clone();
    new_journaled_state.depth = *depth;
    new_journaled_state.journal = journal.clone();
    new_journaled_state.spec = *spec;
    new_journaled_state.warm_preloaded_addresses = warm_preloaded_addresses.clone();

    let context = Context {
        tx: env.tx,
        block: env.block,
        cfg: env.cfg,
        journaled_state: new_journaled_state,
        chain: (),
        error: Ok(()),
    };

    let inspector_context = InspectorContext::<InspectorT, BlockT, TxT, CfgT, Backend>::new(context, inspector);

    let handler = inspector_handler::<
        InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
        EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        PrecompileT,
    >();

    let mut evm = Evm::<
        EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
        InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
        InspectorHandler<
            InspectorContext<InspectorT, BlockT, TxT, CfgT, Backend>,
            EVMError<<Backend as Database>::Error, <TxT as Transaction>::TransactionError>,
            PrecompileT,
        >,
    >::new(inspector_context, handler);

    let result = evm.transact()?;

    // Persist the changes to the original backend.
    journaled_state.database.commit(result.state);
    update_state(&mut journaled_state.state, &mut journaled_state.database)?;

    Ok(())
}

/// Mimics https://github.com/foundry-rs/foundry/blob/25cc1ac68b5f6977f23d713c01ec455ad7f03d21/crates/evm/core/src/backend/mod.rs#L1968
/// Omits persistent accounts (accounts that should be kept persistent when switching forks) for simplicity.
pub fn update_state<DB: Database>(state: &mut EvmState, db: &mut DB) -> Result<(), DB::Error> {
    for (addr, acc) in state.iter_mut() {
        acc.info = db.basic(*addr)?.unwrap_or_default();
        for (key, val) in acc.storage.iter_mut() {
            val.present_value = db.storage(*addr, *key)?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cheatcodes_inspector() {
        type InspectorT<'cheatcodes> = &'cheatcodes mut Cheatcodes<BlockEnv, TxEnv, CfgEnv>;
        type ErrorT = EVMError<<Backend as Database>::Error, <TxEnv as Transaction>::TransactionError>;
        type InspectorContextT<'cheatcodes> =
            InspectorContext<InspectorT<'cheatcodes>, BlockEnv, TxEnv, CfgEnv, Backend>;
        type PrecompileT<'cheatcodes> = EthPrecompileProvider<InspectorContextT<'cheatcodes>, ErrorT>;

        let backend = Backend::default();
        let mut inspector = Cheatcodes::<BlockEnv, TxEnv, CfgEnv>::default();
        let env = Env::mainnet();

        let context = Context::builder()
            .with_block(env.block)
            .with_tx(env.tx)
            .with_cfg(env.cfg)
            .with_db(backend);
        let inspector_context =
            InspectorContext::<InspectorT, BlockEnv, TxEnv, CfgEnv, Backend>::new(context, &mut inspector);
        let handler = inspector_handler::<
            InspectorContext<InspectorT, BlockEnv, TxEnv, CfgEnv, Backend>,
            EVMError<<Backend as Database>::Error, <TxEnv as Transaction>::TransactionError>,
            PrecompileT,
        >();

        let mut evm = Evm::<
            EVMError<<Backend as Database>::Error, <TxEnv as Transaction>::TransactionError>,
            InspectorContext<InspectorT, BlockEnv, TxEnv, CfgEnv, Backend>,
            InspectorHandler<
                InspectorContext<InspectorT, BlockEnv, TxEnv, CfgEnv, Backend>,
                EVMError<<Backend as Database>::Error, <TxEnv as Transaction>::TransactionError>,
                PrecompileT,
            >,
        >::new(inspector_context, handler);

        evm.transact().unwrap();

        // This assertion succeeds
        assert_eq!(evm.context.inspector.call_count, 2);

        // The following assertions fail as the counters are zero, because we need to clone the `Backend` in
        // `Cheatcodes::apply_cheatcode`
        assert_eq!(
            evm.context.inner.journaled_state.database.method_with_inspector_counter,
            1
        );
        assert_eq!(
            evm.context
                .inner
                .journaled_state
                .database
                .method_without_inspector_counter,
            1
        );
    }
}
