//! Experiments with multichain REVM for Foundry-style Solidity test cheatcodes to provide feedback on the REVM
//! implementation.
//!
//! The code below mimics relevant parts of the implementation of the [`transact`](https://book.getfoundry.sh/cheatcodes/transact)
//! and [`rollFork(uint256 forkId, bytes32 transaction)`](https://book.getfoundry.sh/cheatcodes/roll-fork#rollfork)
//! cheatcodes that proved difficult to implement with the new interface.
//! Both of these cheatcodes initiate transactions from a call step in the cheatcode inspector.

pub mod custom_journaled_state;

use std::{convert::Infallible, fmt::Debug};

use revm::{
    context::{BlockEnv, Cfg, CfgEnv, TxEnv},
    context_interface::{
        host::{SStoreResult, SelfDestructResult},
        journaled_state::{AccountLoad, JournalCheckpoint, StateLoad, TransferError},
        result::{EVMError, InvalidTransaction},
        Block, Journal, Transaction,
    },
    handler::EthPrecompileProvider,
    handler_interface::PrecompileProvider,
    precompile::{Address, B256},
    specification::hardfork::SpecId,
    state::{Account, EvmState, TransientStorage},
    Context, Database, DatabaseCommit, Evm, JournalEntry,
};
use revm_bytecode::Bytecode;
use revm_database::InMemoryDB;
use revm_inspector::{
    inspector_handler, inspectors::TracerEip3155, GetInspector, Inspector, InspectorContext, InspectorHandler,
    JournalExt,
};
use revm_interpreter::{interpreter::EthInterpreter, CallInputs, CallOutcome};
use revm_primitives::{Log, U256};

use crate::custom_journaled_state::CustomJournaledState;

/// Backend for cheatcodes.
/// The problematic cheatcodes are only supported in fork mode, so we'll omit the non-fork behavior of the `Backend`.
#[derive(Clone, Debug)]
pub struct Backend {
    /// In fork mode, Foundry stores (`JournaledState`, `Database`) pairs for each fork.
    db: InMemoryDB,
    journaled_state: CustomJournaledState,
    /// Counters to be able to assert that we mutated the object that we expected to mutate.
    method_with_inspector_counter: usize,
    method_without_inspector_counter: usize,
}

impl Backend {
    pub fn new(spec: SpecId, db: InMemoryDB) -> Self {
        Self {
            db,
            journaled_state: CustomJournaledState::new(spec),
            method_with_inspector_counter: 0,
            method_without_inspector_counter: 0,
        }
    }
}

// Based on https://github.com/bluealloy/revm/blob/17c4543ef559ef4011fa6c155bc981b1f504f33c/crates/context/src/journaled_state.rs
impl Journal for Backend {
    type Database = InMemoryDB;
    type FinalOutput = (EvmState, Vec<Log>);

    fn new(database: InMemoryDB) -> Self {
        Self::new(SpecId::LATEST, database)
    }

    fn db(&self) -> &Self::Database {
        &self.db
    }

    fn db_mut(&mut self) -> &mut Self::Database {
        &mut self.db
    }

    fn sload(&mut self, address: Address, key: U256) -> Result<StateLoad<U256>, <Self::Database as Database>::Error> {
        self.journaled_state.sload(&mut self.db, address, key)
    }

    fn sstore(
        &mut self,
        address: Address,
        key: U256,
        value: U256,
    ) -> Result<StateLoad<SStoreResult>, <Self::Database as Database>::Error> {
        self.journaled_state.sstore(&mut self.db, address, key, value)
    }

    fn tload(&mut self, address: Address, key: U256) -> U256 {
        self.journaled_state.tload(address, key)
    }

    fn tstore(&mut self, address: Address, key: U256, value: U256) {
        self.journaled_state.tstore(address, key, value)
    }

    fn log(&mut self, log: Log) {
        self.journaled_state.log(log)
    }

    fn selfdestruct(&mut self, address: Address, target: Address) -> Result<StateLoad<SelfDestructResult>, Infallible> {
        self.journaled_state.selfdestruct(&mut self.db, address, target)
    }

    fn warm_account(&mut self, address: Address) {
        self.journaled_state.warm_preloaded_addresses.insert(address);
    }

    /// Returns call depth.
    #[inline]
    fn depth(&self) -> usize {
        self.journaled_state.depth
    }

    fn warm_account_and_storage(
        &mut self,
        address: Address,
        storage_keys: impl IntoIterator<Item = U256>,
    ) -> Result<(), <Self::Database as Database>::Error> {
        self.journaled_state
            .initial_account_load(&mut self.db, address, storage_keys)?;
        Ok(())
    }

    fn set_spec_id(&mut self, spec_id: SpecId) {
        self.journaled_state.spec = spec_id;
    }

    fn transfer(&mut self, from: &Address, to: &Address, balance: U256) -> Result<Option<TransferError>, Infallible> {
        // TODO : Handle instruction result
        self.journaled_state.transfer(&mut self.db, from, to, balance)
    }

    fn touch_account(&mut self, address: Address) {
        self.journaled_state.touch(&address);
    }

    fn inc_account_nonce(&mut self, address: Address) -> Result<Option<u64>, Infallible> {
        Ok(self.journaled_state.inc_nonce(address))
    }

    fn load_account(&mut self, address: Address) -> Result<StateLoad<&mut Account>, Infallible> {
        self.journaled_state.load_account(&mut self.db, address)
    }

    fn load_account_code(&mut self, address: Address) -> Result<StateLoad<&mut Account>, Infallible> {
        self.journaled_state.load_code(&mut self.db, address)
    }

    fn load_account_delegated(&mut self, address: Address) -> Result<AccountLoad, Infallible> {
        self.journaled_state.load_account_delegated(&mut self.db, address)
    }

    fn checkpoint(&mut self) -> JournalCheckpoint {
        self.journaled_state.checkpoint()
    }

    fn checkpoint_commit(&mut self) {
        self.journaled_state.checkpoint_commit()
    }

    fn checkpoint_revert(&mut self, checkpoint: JournalCheckpoint) {
        self.journaled_state.checkpoint_revert(checkpoint)
    }

    fn set_code_with_hash(&mut self, address: Address, code: Bytecode, hash: B256) {
        self.journaled_state.set_code_with_hash(address, code, hash);
    }

    fn clear(&mut self) {
        // Clears the JournaledState. Preserving only the spec.
        self.journaled_state.state.clear();
        self.journaled_state.transient_storage.clear();
        self.journaled_state.logs.clear();
        self.journaled_state.journal = vec![vec![]];
        self.journaled_state.depth = 0;
        self.journaled_state.warm_preloaded_addresses.clear();
    }

    fn create_account_checkpoint(
        &mut self,
        caller: Address,
        address: Address,
        balance: U256,
        spec_id: SpecId,
    ) -> Result<JournalCheckpoint, TransferError> {
        // Ignore error.
        self.journaled_state
            .create_account_checkpoint(caller, address, balance, spec_id)
    }

    fn finalize(&mut self) -> Result<Self::FinalOutput, <Self::Database as Database>::Error> {
        let CustomJournaledState {
            state,
            transient_storage,
            logs,
            depth,
            journal,
            // kept, see [Self::new]
            spec: _,
            warm_preloaded_addresses: _,
        } = &mut self.journaled_state;

        *transient_storage = TransientStorage::default();
        *journal = vec![vec![]];
        *depth = 0;
        let state = std::mem::take(state);
        let logs = std::mem::take(logs);

        Ok((state, logs))
    }
}

impl JournalExt for Backend {
    fn logs(&self) -> &[Log] {
        &self.journaled_state.logs
    }

    fn last_journal(&self) -> &[JournalEntry] {
        self.journaled_state.journal.last().expect("Journal is never empty")
    }
}

/// Used in Foundry to provide extended functionality to cheatcodes.
/// The methods are called from the `Cheatcodes` inspector.
pub trait DatabaseExt: Journal {
    /// Mimics `DatabaseExt::transact`
    /// See `commit_transaction` for the generics
    fn method_that_takes_inspector_as_argument<InspectorT, BlockT, TxT, CfgT, PrecompileT>(
        &mut self,
        env: Env<BlockT, TxT, CfgT>,
        inspector: InspectorT,
    ) where
        InspectorT: Inspector<Context = Context<BlockT, TxT, CfgT, InMemoryDB, Backend>, InterpreterTypes = EthInterpreter>
            + GetInspector<Inspector = InspectorT>,
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
            Error = EVMError<Infallible, <TxT as Transaction>::TransactionError>,
        >;

    /// Mimics `DatabaseExt::roll_fork_to_transaction`
    fn method_that_constructs_inspector<BlockT, TxT, CfgT /* PrecompileT */>(&mut self, env: Env<BlockT, TxT, CfgT>)
    where
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
        Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
        Error = EVMError<Infallible, <TxT as Transaction>::TransactionError>,
    >
    */
}

impl DatabaseExt for Backend {
    fn method_that_takes_inspector_as_argument<InspectorT, BlockT, TxT, CfgT, PrecompileT>(
        &mut self,
        env: Env<BlockT, TxT, CfgT>,
        inspector: InspectorT,
    ) where
        InspectorT: Inspector<Context = Context<BlockT, TxT, CfgT, InMemoryDB, Backend>, InterpreterTypes = EthInterpreter>
            + GetInspector<Inspector = InspectorT>,
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
            Error = EVMError<Infallible, <TxT as Transaction>::TransactionError>,
        >,
    {
        commit_transaction::<InspectorT, BlockT, TxT, CfgT, PrecompileT>(self, env, inspector).unwrap();
        self.method_with_inspector_counter += 1;
    }

    fn method_that_constructs_inspector<BlockT, TxT, CfgT /* , PrecompileT */>(&mut self, env: Env<BlockT, TxT, CfgT>)
    where
        /*InspectorT: Inspector<
            Context = Context<BlockT, TxT, CfgT, InMemoryDB, Backend>,
            InterpreterTypes = EthInterpreter,
        > + GetInspector<Inspector = InspectorT>,*/
        BlockT: Block,
        TxT: Transaction,
        <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
        CfgT: Cfg,
        /*PrecompileT: PrecompileProvider<
            Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
            Error = EVMError<Infallible, <TxT as Transaction>::TransactionError>,
        >,*/
    {
        let inspector = TracerEip3155::new(Box::new(std::io::sink()));
        commit_transaction::<
            // Generic interpreter types are not supported yet in the `Evm` implementation
            TracerEip3155<Context<BlockT, TxT, CfgT, InMemoryDB, Backend>, EthInterpreter>,
            BlockT,
            TxT,
            CfgT,
            // Since we can't have a generic precompiles type param as explained in the trait definition, we're using a
            // concrete type here.
            EthPrecompileProvider<
                InspectorContext<
                    TracerEip3155<Context<BlockT, TxT, CfgT, InMemoryDB, Backend>, EthInterpreter>,
                    BlockT,
                    TxT,
                    CfgT,
                    InMemoryDB,
                    Backend,
                >,
                EVMError<Infallible, <TxT as Transaction>::TransactionError>,
            >,
        >(self, env, inspector)
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
    fn apply_cheatcode(&mut self, context: &mut Context<BlockT, TxT, CfgT, InMemoryDB, Backend>) {
        // `transact` cheatcode would do this
        context
            .journaled_state
            .method_that_takes_inspector_as_argument::<&mut Self, BlockT, TxT, CfgT, EthPrecompileProvider<
                InspectorContext<&mut Self, BlockT, TxT, CfgT, InMemoryDB, Backend>,
                EVMError<Infallible, <TxT as Transaction>::TransactionError>,
            >>(
                Env {
                    block: context.block.clone(),
                    tx: context.tx.clone(),
                    cfg: context.cfg.clone(),
                },
                self,
            );

        // `rollFork(bytes32 transaction)` cheatcode would do this
        context.journaled_state.method_that_constructs_inspector(Env {
            block: context.block.clone(),
            tx: context.tx.clone(),
            cfg: context.cfg.clone(),
        });
    }
}

impl<BlockT, TxT, CfgT> Inspector for Cheatcodes<BlockT, TxT, CfgT>
where
    BlockT: Block + Clone,
    TxT: Transaction + Clone,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg + Clone,
{
    type Context = Context<BlockT, TxT, CfgT, InMemoryDB, Backend>;
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
    backend: &mut Backend,
    env: Env<BlockT, TxT, CfgT>,
    inspector: InspectorT,
) -> Result<(), EVMError<Infallible, <TxT as Transaction>::TransactionError>>
where
    InspectorT: Inspector<
            Context = Context<BlockT, TxT, CfgT, InMemoryDB, Backend>,
            // Generic interpreter types are not supported yet in the `Evm` implementation
            InterpreterTypes = EthInterpreter,
        > + GetInspector<Inspector = InspectorT>,
    BlockT: Block,
    TxT: Transaction,
    <TxT as Transaction>::TransactionError: From<InvalidTransaction>,
    CfgT: Cfg,
    PrecompileT: PrecompileProvider<
        Context = InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
        Error = EVMError<Infallible, <TxT as Transaction>::TransactionError>,
    >,
{
    // Create new journaled state and backend with the same DB and journaled state as the original for the transaction.
    // This new backend and state will be discarded after the transaction is done and the changes are applied to the
    // original backend.
    // Mimics https://github.com/foundry-rs/foundry/blob/25cc1ac68b5f6977f23d713c01ec455ad7f03d21/crates/evm/core/src/backend/mod.rs#L1950-L1953
    let new_backend = backend.clone();

    let context = Context {
        tx: env.tx,
        block: env.block,
        cfg: env.cfg,
        journaled_state: new_backend,
        chain: (),
        error: Ok(()),
    };

    let inspector_context =
        InspectorContext::<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>::new(context, inspector);

    let handler = inspector_handler::<
        InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
        EVMError<Infallible, <TxT as Transaction>::TransactionError>,
        PrecompileT,
    >();

    let mut evm = Evm::<
        EVMError<Infallible, <TxT as Transaction>::TransactionError>,
        InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
        InspectorHandler<
            InspectorContext<InspectorT, BlockT, TxT, CfgT, InMemoryDB, Backend>,
            EVMError<Infallible, <TxT as Transaction>::TransactionError>,
            PrecompileT,
        >,
    >::new(inspector_context, handler);

    let result = evm.transact()?;

    // Persist the changes to the original backend.
    backend.db.commit(result.state);
    update_state(&mut backend.journaled_state.state, &mut backend.db)?;

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
        type ErrorT = EVMError<Infallible, <TxEnv as Transaction>::TransactionError>;
        type InspectorContextT<'cheatcodes> =
            InspectorContext<InspectorT<'cheatcodes>, BlockEnv, TxEnv, CfgEnv, InMemoryDB, Backend>;
        type PrecompileT<'cheatcodes> = EthPrecompileProvider<InspectorContextT<'cheatcodes>, ErrorT>;

        let backend = Backend::new(SpecId::LATEST, InMemoryDB::default());
        let mut inspector = Cheatcodes::<BlockEnv, TxEnv, CfgEnv>::default();
        let env = Env::mainnet();

        let context = Context {
            tx: env.tx,
            block: env.block,
            cfg: env.cfg,
            journaled_state: backend,
            chain: (),
            error: Ok(()),
        };
        let inspector_context =
            InspectorContext::<InspectorT, BlockEnv, TxEnv, CfgEnv, InMemoryDB, Backend>::new(context, &mut inspector);
        let handler = inspector_handler::<
            InspectorContext<InspectorT, BlockEnv, TxEnv, CfgEnv, InMemoryDB, Backend>,
            EVMError<Infallible, <TxEnv as Transaction>::TransactionError>,
            PrecompileT,
        >();

        let mut evm = Evm::<
            EVMError<Infallible, <TxEnv as Transaction>::TransactionError>,
            InspectorContext<InspectorT, BlockEnv, TxEnv, CfgEnv, InMemoryDB, Backend>,
            InspectorHandler<
                InspectorContext<InspectorT, BlockEnv, TxEnv, CfgEnv, InMemoryDB, Backend>,
                EVMError<Infallible, <TxEnv as Transaction>::TransactionError>,
                PrecompileT,
            >,
        >::new(inspector_context, handler);

        evm.transact().unwrap();

        assert_eq!(evm.context.inspector.call_count, 2);
        assert_eq!(evm.context.inner.journaled_state.method_with_inspector_counter, 1);
        assert_eq!(evm.context.inner.journaled_state.method_without_inspector_counter, 1);
    }
}
