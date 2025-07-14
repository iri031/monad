# Consensus events

## _Beware_: the events you see may not actually happen!

Execution events are "trace" information reported directly from the EVM. In
Category Lab's implementation of a Monad node, execution and consensus are
decoupled, as they are in most legacy Ethereum clients. That is, consensus
and execution are not _just_ different algorithms, but completely separate
programs that communicate with each other. Consensus is the algorithm (and
the daemon) which decides whether or not a potential block will become part
of the blockchain.

Monad has considerably more parallelism in its fundamental design than
legacy Ethereum does: consensus is allowed to run in parallel with execution,
and can vote on a block even before that block has finished executing.[^1]

Typically though, _block execution will finish before the consensus algorithm
does_. This means that you will find out _sometime later_, whether the block
and its transactions (and their state effects) were actually committed to the
Monad blockchain or not. At the time you see the execution events, you will
not know if they "actually happen" or not.

The fundamental reason why consensus is slower is that it is a distributed
algorithm that needs to run over the public Internet. Several back-and-forth
exchanges are needed, and these must reach data centers all over the world,
while being robust to real-world network latency issues. For this reason,
consensus rounds (instances of voting on a particular block) are
approximately 500 milliseconds long. In the typical case, it takes two of
these 0.5 second rounds to finalize a block.

Thus when you see an execution event, you're probably seeing it ~1 second
before consensus will decided whether or not to append the associated block to
the blockchain (although half-way through, you will receive a notification
that most of risk of reversion has been removed).

So you should be aware of two things:

The events you see are describing what the effects and outputs of transactions
_will_ be, but _only if_ the block ends up getting finalized on the Monad
blockchain. You will find out if that happens later, via a few special event
types. Despite these special events being part of the "execution events" SDK,
they ultimately come from the consensus software: they explicitly communicate
what consensus decided to do with the block, after you have already seen the
events created by that block's execution.

[1]: If you are wondering how this is possible, it's because a block whose
format is correct (consists of only valid transactions and obeys all the
protocol rules) is guaranteed to execute and eventually halt in the EVM.
It is possible to perform this validation _without_ actually executing the
transactions and computing the final state effects of the block.

## Proposed blocks, block tags, and consensus events

The API documentation for the `struct monad_exec_block_tag` explains the
basics:

> Once a block is canonically appended to the block chain, it becomes uniquely
> identified by a (sequentially increasing) block number, also called a "block
> height." The inclusion of a block on the blockchain is the goal of the
> consensus algorithm, and is called "finalization."
>
> When a block it first constructed, it is constructed assuming it will become
> the next block number, `B`. Prior to finalization, consensus nodes are still
> trying to agree whether or not this candidate block will become block `B`.
>
> During this time, multiple blocks could be proposed, some of which are
> competing candidates to become the same block number `B`. For performance
> reasons, the execution daemon is allowed to speculatively execute blocks in
> the EVM before consensus attempts to finalize them. Consequently, even blocks
> that never become part of the blockchain may produce execution events; the
> execution event stream may describe transactions that "never happen" on
> chain.
>
> Thus, when a block number is seen during an event, e.g., `BLOCK_START`, it
> is not necessarily the case that the corresponding block will be added to
> the blockchain as this block number (or at all).
>
> The information in the "tag" object is used to track a block as it is
> operated on by the consensus algorithm. The (not yet unique) `block_number`
> is the number the block _will_ have, if it eventually gets finalized. The
> `id` field uniquely identifies the block contents, vs. all the other
> proposals of different blocks to become the same `block_number`. `id` can be
> used to track this specific block before finalization.

The above documentation is describing the following structure:

```
struct monad_exec_block_tag
{
    monad_c_bytes32 id;    ///< Monad consensus unique ID for block
    uint64_t block_number; ///< Proposal is to become this block
};
```

These "block tags" appear in three kinds of event payloads, corresponding
to the first three phases of the consensus protocol.

### First consensus event: **`BLOCK_START`**

```c
/// Event recorded at the start of block execution
struct monad_exec_block_start
{
    struct monad_exec_block_tag
        block_tag;                      ///< Execution is for this block
    uint64_t block_round;               ///< Round when block was proposed
    uint64_t epoch;                     ///< Epoch when block was proposed
    monad_c_bytes32 parent_eth_hash;    ///< Hash of Ethereum parent block
    monad_c_uint256_ne chain_id;        ///< Block chain we're associated with
    struct monad_c_eth_block_exec_input
        exec_input;                     ///< Ethereum execution inputs
};
```

When a new block is proposed by a leader (a Monad validator node), it is sent
to all consensus nodes to be voted on. If the block is valid (i.e., follows
all protocol rules), the consensus node will vote "yes" for it, and schedule
it for speculative execution immediately. Shortly after this happens --
even as the "yes" vote is starting to be transmitted over the Internet --
the execution daemon begins executing the proposed block in the EVM. A few
milliseconds later, the EVM will begin emitting events for this block.

The first event recorded by the EVM is a `BLOCK_START` event, whose event
payload contains a `block_tag` field that introduces the unique ID for the
block and the block number it will eventually have, if it gets voted in.
Almost all execution events (transaction logs, call frames, receipts, etc.)
occur between the `BLOCK_START` and `BLOCK_END` events. In the current
implementation, block execution is never pipelined, so all events between
`BLOCK_START` and `BLOCK_END` pertain to a single block, and there will not
be another `BLOCK_START` until the current block is ended.

Unlike the other events in this list, `BLOCK_START` is both a "consensus
event" (it means consensus has received a block proposal) and an "EVM event,"
meaning that execution information is being made available to you. The other
events in this list are pure consensus events: they tell you what happened
to the proposed block in the consensus algorithm, after you've already seen
all of its EVM events.

### Second consensus event: **`BLOCK_QC`**

```c
/// Event recorded when a proposed block obtains a quorum certificate
struct monad_exec_block_qc
{
    struct monad_exec_block_tag
        block_tag;              ///< QC for proposal with this block
    uint64_t round;             ///< Round of proposal vote
    uint64_t epoch;             ///< Epoch of proposal vote
};
```

In parallel with a proposed block being executed, the consensus algorithm is
conducting a first round vote on whether or not that block will be appended
to the blockchain. The goal of this referendum is to produce a "quorum"
(minimum number of required votes for referendum to pass) of "yes" votes.

The vote is conducted by gathering cryptographic signatures, and when a
quorum of nodes sign a "yes" vote, their aggregate signature is called a
"quorum certificate." Having a quorum certificate means that the proposal has
passed the first round of voting. When this happens, a `BLOCK_QC` event will
be recorded with the same `block_tag` as was present in the `BLOCK_START`
payload, when the proposed block was speculatively executed earlier.

A few things to note about `BLOCK_QC`:

#### A block might never get a QC

A proposed block might never receive a QC, if its consensus vote fails. When
you see `BLOCK_START` (and all subsequent EVM events), the only thing you know
is that the local node has voted "yes", but it remains to be seen whether
enough other nodes will agree or not.

The most common reason that a block does not get voted in is network latency
issues. Suppose, for example, that both your node and the leader are in
Australia, and there is significant congestion with the cross-continental
network traffic. In that case, most of the blockchain nodes may not learn
about the proposal before the timeout period expires, and the vote will fail.
Note that you will not be told that the votes fails. The failure of the vote
is _implicit_, but you can tell it is happening because of the next property.

##### For some block number `N`, _some_ proposed block will get a QC

If you do not receive a `BLOCK_QC` for a particular block with block number
`N`, then at some other time you will receive a different proposed block to
become block `N`. That is, you'll see a different `BLOCK_START` (where
`block_tag.block_number` is also `N`, but `block_tag.id` is different). This
will be followed by all of the new block's EVM events, followed eventually
by a `BLOCK_QC` for this new block.

A sequence like the following may occur: 

- You see all of the EVM events (`BLOCK_START`, `BLOCK_END`, and everything
  in between) for some block `B1`, which is proposed to become block number
  `N`
- You see a _different_ block, `B2` (and all of its execution events) also
  competing to become `B2`
- `B2` receives a QC, and this is the only thing that happens. Namely, `B1`
  does _not_ receive an explicit "abandonment" event: it is just never
  mentioned again, and is implicitly abandoned by the network endorsing
  another block with the same number

##### QC does not mean it's on the blockchain

A block does _not_ become canonically appended to the blockchain when it
receives a QC. Monad's consensus algorithm uses two rounds of voting, and
each round reduces the risk that a proposed block can be reverted. In the
current iteration of the algorithm, having a QC (first round vote) removes
the most common kinds of risks, but some risk of being reverted remains until
a second round of voting occurs. If the second round vote is successful, only
then will the block become "finalized" (which is discussed next).

Having a QC removes the risk that a block will be "lost" due to the most
common issues such as network outages and latency issues. If network problems
occur after QC a received, i.e., if the second round of voting is disrupted,
the algorithm will continue conducting the same second round vote until enough
of the network is restored for the vote to succeed.

How can a block with a QC still be reverted then? It can happen if the leader
of the second round vote is malicious and wants to rig the vote, causing the
second round of voting to fail. Blockchains employ various schemes to prevent
this from occurring too frequently, but it is a fundamental issue that is
faced by all BFT consensus algorithms. It is typically solved by introducing
a second round of voting.

### Third consensus event: **`BLOCK_FINALIZED`**

```c
/// Event recorded when consensus finalizes a block
typedef struct monad_exec_block_tag monad_exec_block_finalized;
```

The finalized event payload does not have any information that isn't already
part of the block tag, so the payload is just the tag of the block that gets
finalized.

When a block with height `N` is finalized, it _implicitly_ abandons all
other proposed blocks with the same block height `N`. Such blocks could be
in either the proposed or the QC state. We say the abandonment is implicit
because no event will be recorded to explicitly announce the abandonment of
previous seen block tag.

If the reader has been tracking some state associated with unfinalized blocks,
then upon every `BLOCK_FINALIZED` event, that read must check for any blocks
(1) with the same block number, but (2) with a different ID, and discard the
state of those blocks. Those blocks will never be appended to the blockchain
and the associated transactions and their effects -- whose execution events
you have already seen -- will never occur.

### Fourth consensus event: **`BLOCK_VERIFIED`**

```c
/// Event recorded when consensus verifies the state root of a finalized block
struct monad_exec_block_verified
{
    uint64_t block_number; ///< Number of verified block
};
```

The consensus algorithm produces one last event for a block, called
`BLOCK_VERIFIED`. This time, it is sufficient to identify the block only by
its block number. Because verified blocks are already finalized, they are
part of the canonical blockchain and cannot be reverted without a hard fork.
Thus, we no longer need the block tag.

The verified state is a consequence of Monad's parallelized execution. Recall
that a consensus node votes on a block _before_ its execution is complete.
This implies that consensus must be voting on the block's execution inputs,
but _not_ on the block's execution outputs.

Consensus nodes cannot be voting, for example, on the correct value of the
state root produced by the execution of the block, because they don't know
what it is (remember, it is being computed in parallel with the vote
occuring). This means that an event such as `BLOCK_QC` does not certify the
correctness of any output fields in the Ethereum block header such as
`state_root`, `receipts_root`, etc.

This is possible because any well-formed Ethereum block will have completely
deterministic effects on the blockchain state, when executed by a conforming
EVM implementation. Thus it is safe to append a block onto the blockchain,
knowing that everyone will agree on its behavior, even if we don't know
exactly what the behavior will be.

Clearly though, for the blockchain to be reliable, consensus nodes _must_
eventually vote on the correctness of the executon outputs. Suppose they did
not, and further suppose that a bug existed in some execution nodes but not
in others (perhaps running a different version of the client software). If
there were no mechanism to feed the execution outputs back into consensus
decisions, the state could become forked without anyone noticing. Consensus
proposals _start_ by assuming that all execution nodes will compute the
correct state, but to prevent bugs and malicious actions from compromising
the network, it must check that this happens eventually.

Here is how Monad solves this issue:

To give execution ample time to finish, execution outputs for block `B`
are not incorporated into the consensus protocol until three rounds in the
future, alongside the proposal of block `B+3`. When _this_ proposal is
finalized (ideally two rounds later, during the proposal of block `B+5`),
then a supermajority of nodes will have voted for the correct values of
the execution outputs.

To understand more, read [here](https://docs.monad.xyz/monad-arch/consensus/asynchronous-execution).

To roughly summarize the difference:

- `BLOCK_FINALIZED` means the block's definition (i.e., its transactions) are definitely part of the block chain
- `BLOCK_VERIFIED` means that a supermajority stake's worth of other nodes have verified that your local node's computation of the state changes of these transactions match the same values as the supermajority's
