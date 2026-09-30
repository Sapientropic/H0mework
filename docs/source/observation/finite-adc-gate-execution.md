# Finite ADC arithmetic gate execution

## Fixed source graphs

The receiver's 128-bit subtraction, multiplication, addition, signed comparison
and unsigned comparison each have a fixed source expression over two variables.
Lean Std's verified bitblaster generates their finite AND/inverter graphs.
Runtime operands do not participate in graph compilation.

Word graphs expose an `AIG.RefVecEntry BVBit 128`: declarations, the generated
DAG invariant and 128 output references. Boolean graphs expose one entrypoint.
Both use the same two-operand assignment.

`finiteADC128GateReadWord` generates one shared value table and reads its
output references into a BitVec; the Boolean read uses the same executor.
Correctness recovers Std's denotation from that table, consumes
`denote_bitblast`, then the source-expression semantics:

```text
fixed expression → generated AIG
runtime operands → input assignment → graph outputs
graph outputs = the specified BitVec operation, for every operand pair.
```

Subtraction is lowered to addition with inverted bits plus one. Signed order
retains the sign-bit correction to unsigned order. These distinctions matter:
negative differences use modular multiplication, while signed and unsigned
order cannot be interchanged.

## Source-DAG execution

`AIGExecutionPrefix graph` stores a source-sized `Vector Bool` buffer and one
finite written cursor. Boot initializes its fixed slots to zero while the
written frontier is empty. These zeroes are not gate answers: the initialized
value can differ from the eventually generated value, and unfinished output is
rejected. `aigExecutionStep` selects the declaration at the cursor, reads atoms
from the current assignment and fanins directly from the buffer. Source `hdag`
proves those fanins lie strictly before the written frontier.

The actual update uses `Vector.set`, never `push`; capacity is fixed at boot.
The existing `Nat.repeat` engine generates one value per declaration:

```text
cursorAfter(ticks) = min(ticks, graph.decls.size)
bufferAfter(ticks).size = graph.decls.size
run = valuesAfter(graph.decls.size).
```

The compatibility `.values` surface exposes only the written prefix. It is a
proof/readout view, absent from the runtime step and completed reads. Frontier
write and other-slot preservation are proved for the actual buffer; induction
from zero boot proves every unwritten cell remains zero.

Consistency with Std denotation is proved from empty and preserved by the
actual step; it is not a premise of `aigExecutionRun`.
`aigExecutionRun_read_eq_denote` handles every reference and its inversion.
The whole-graph read mouth stays unfinished until the complete table exists.

`aigExecutionReadVector` runs the graph once, then all word bits look up that
same table. These cached reads are installed in the original five public
gate-operation APIs. Consequently the existing receiver and physical next
consume the new execution without another parallel receiver.

## Complete raw admission

Three fixed AIGs share one addressed raw-input language: the 61 packet predicates
(header bound plus sixty word ranges), twenty positive spans, and their
81-predicate conjunction. Static compilation depends only on ADC resolution
and counter width. The 62 assignment slots contain the header, a clamped
configuration bound and sixty raw words—not an acceptance result.

Clamping `lastTick` to the largest encodable header preserves its comparison
with every possible packet header, including width zero and oversized bounds.
The whole admission theorem has no caller-validity premise. Word-range guards
are used before proving that the decoder's common offset cancels from span
order and from the 128-bit differences.

`FiniteADCRawInstalledProgram` stores the two complete packet/calibration
entrypoints, including their output references. Its compiler takes only ADC
code and counter width; no packet or verdict enters compilation. Source
equalities identify the stored graphs with the existing bitblaster outputs.
They rule out a substituted graph or a flipped terminal reference.

`finiteADCRawMicroStepWithProgram` reads these stored declarations and refs.
`AfterWithProgram` captures the installed program before entering the iterator;
`MicroExecute` derives its deadline from the stored graph sizes. The code-only
`ExecuteFor` convenience entry compiles once before this execution. An explicit
program can be reused across packets. The physical current-driven core now
receives one explicit boot installation and reuses it across its steps. The
frame-observation convenience interface constructs the canonical installation;
separately invoking that interface is not a once-only allocation guarantee.

## One raw occurrence, two representations

`FiniteADCRawReceiverState` retains the packet through the parsed/calibrated
phases. The actual packet-gate branch generates its erased range guard;
calibration executes separately, so a valid packet with invalid calibration
still reaches parsed-some before becoming calibrated-none.

Runtime differences zero-extend the raw words and use the existing gate
subtractor. There is no signed decoder followed by re-packing on this path.
The old typed state is a logical restriction, `finiteADCRawReceiverReadout`;
it is not called by the runtime or by the independent raw output function.

`finiteADCRawReceiverStep_commutes` proves semiconjugacy for every raw state.
The existing `Function.Semiconj.iterate_right` transfers all finite prefixes
to the original typed machine. Eight-stage completion, earlier output absence
and both rejection paths follow without another induction engine.

The original `finiteADCPhysicalGateExecutionAt` now returns this raw state.
Feedback reads its raw terminal output directly; the existing
`finiteADCPhysicalGateNextAt` generates the same literal next physical
current. Rooted frontier, actual endpoint splice, fixed counters and the new
sample receipt remain installed.

The [physical feedback mechanism](finite-adc-physical-feedback-continuation.md)
owns these outer continuation laws; they are not reproved as a gate-specific
recurrence.

## Owned microclock and physical deadline

`AIGOwnedProgress` fixes the graph and assignment and retains the actual buffer
state, including its unique cursor. Its erased lineage is generated from zero
boot and actual step. `AIGOwnedBatch` stores raw source-sized job buffers with
one shared cursor, not a repeated header per job. Its compatibility `.tables`
view is not used by `Step`, `Job` or completed reads. Both ownership laws fix the
complete buffer, including the initialized but unwritten tail; changing a hidden
tail bit cannot produce an owned current with the same visible prefix.

The actual step saturates the stored cursor at the source graph's end. Its
`ticks` compatibility view is only the cursor value; it is no longer an
unbounded elapsed counter. The table still equals the original source execution
at every external tick, since execution at `min(ticks, size)` equals execution
at `ticks`. Completion fixes the entire owned current, not merely its table.

For a fixed graph and assignment, `aigOwnedProgressEquivCursor` and
`aigOwnedBatchEquivCursor` classify the whole stored state by exactly
`graph.decls.size + 1` positions, including zero-job batches. The inverse runs
the existing history from empty; it does not supply a prefilled runtime cache.
This local storage coordinate does not identify different external clock
attempts or different physical switch occurrences.

`FiniteADCRawMicroState` connects packet admission, calibration, subtraction,
squaring, products, sum, scale and comparison. A phase boots only after the
preceding phase has generated its input. The arithmetic banks contain
40/40/30/10/10 parallel jobs; comparison advances twenty signed and ten unsigned
jobs together.

Every completed phase latches its output in an explicit control tick.
Word outputs are materialized before constructing their register records.
The two final AND layers each materialize a ten-Bool Vector; `finalAnd` and
`done` store these data vectors, not delayed function applications.
The independent output function only reads the stored result.

Compiler verification matters at this boundary: putting `Vector.ofFn` inside
a function-valued return does not force latching, because eta expansion can
move it after the channel argument. The generated IR now shows each array
being constructed before its state constructor. Function views remain
proof/readout interfaces, not evidence of an already executed control tick.

The installed processing count is

```text
packet graph + calibration graph + subtraction graph
+ 3 × multiplication graph + addition graph
+ max(signed-comparison graph, unsigned-comparison graph)
+ 7 phase-latch ticks + 2 AND-control ticks.
```

The remaining-work rank is derived from actual progress. Every positive-rank
step decreases it; every non-rejection step consumes exactly one unit.
A proof-only residual result is invariant under the actual step, and the
existing semiconjugacy iterator transfers that invariant to every prefix.
It does not enter the machine state or runtime execution.

`finiteADCRawMicro_completed` returns exactly the established receiver result
at this deadline for **every raw packet**, without a validity premise.
Accepted packets cannot complete earlier. Rejected packets may finish early
with visible `some none` and idle to the same installed deadline.

The unsigned comparison bank saturates after 896 declarations while the signed
bank continues to 902. Their maximum remaining-work rank still decreases once
per tick; no address wrap or new deadline is introduced.

`finiteADCRawMicroStateAtFinite` proves the entire actual microstate type finite,
with all seven graphs kept abstract. A proof-only finite descriptor covers the
ten constructors, including raw packets, checked packets, finite-domain word
registers, independent owned banks and latched Boolean vectors. It is not called
by the runtime. The physical regression directly consumes this finite digital
carrier at the existing hardware-derived width and bound.

`finiteADCPhysicalMicroNextAt` reads this actual terminal register and uses
the same graph-derived count for the physical switch. The old drive runs up
to that switch; its actual V/I state becomes the next initial. Literal next,
rooted frontier, uniform sample/switch counters and fresh sample receipt
reuse the existing delayed-continuation chain. This longer-delay occurrence
is not identified with the old eight-macrostep occurrence.

## One installation, actual-current physical steps

`compileFiniteADCPhysicalMicroInstallation` takes only hardware and the named
boot initial. The existing uniform bound generates a finite maximum-tick word
and the source program. Counter and program uniqueness follow from their source
equalities, not from a receiver verdict.

`FiniteADCPhysicalInstalledMicroCurrent installation` contains one literal
generated physical run whose sample tick fits that installed bound. Boot
generates admission from the existing command census. The packet reads this
current's recorded tick and sixty ADC words; execution calls `MicroExecute` with
the stored program and stored bound. The current step takes no frame number,
contains no compiler call and does not recover its current from an old orbit.

The actual terminal registers generate feedback, and the old drive's actual
delayed endpoint generates the next initial. The existing core successor bound
then generates the target current's admission into the same installation.
Erasing this local bound commutes with the original delayed physical successor;
`Function.Semiconj.iterate_right` transfers every finite prefix, and the existing
rooted exposure supplies its frontier. No additional continuation calculus is
introduced.

The original `MicroPacketAt`, `MicroExecutionAt` and `MicroNextAt` now observe
this current-driven process. Their former packet, deadline, no-reset, counter,
rooted-next and fresh-receipt mouths remain exact. Direct controls reject a
wrong installed counter, early output, a read-only step, another current's
answer and a replacement endpoint; the generated next is accepted by the same
installed receiver again.

## Verification and scope

The digital carrier is indexed by the existing `FiniteADCResolutionCode`,
counter width and explicit bound. `FiniteADCWirePacketFor` and
`finiteADCRawMicroAfterFor` need no real-valued physical-source object.
Old source-facing packet, gate and execution mouths restrict this one
implementation along `source.adcCode`; no dummy source or second receiver is
constructed. The physical receipt still joins the original hardware, recorded
packet and generated clock. `finiteADCPhysicalMicroExecutionAt_code_restriction`
states this same-occurrence handoff using the generated program-size equality.

The executable batch update uses a finite fold of standard `Array.modify`.
Each raw buffer slot is moved out before its one-address update; the pointwise proof
recovers exactly the old per-job step and preserves source lineage. A
dependent `mapFinIdx` implementation had retained the old outer array and
therefore forced copies of growing inner prefixes. Generated C confirms that
the installed update no longer retains that old-array argument. The fixed-buffer
revision also checks 96 local hot-path callees: no `.values`, `.tables`,
take/extract or push remains on that path. No custom
unsafe primitive is introduced.

Direct controls cover signed versus unsigned comparison, a negative modular
square, early output, invalid packets, invalid calibration, actual physical
packet readback, the rooted next and output-side receipt regeneration.

The executor's direct controls cover assignment override, shared fanins,
inverted references, actual prefix values, early output, unwritten future
slots, forged short tables and rejection of cyclic source declarations.
Runtime evaluation of the actual 128-bit graphs also exercises addition,
subtraction, multiplication and the signed/unsigned distinction.

Additional controls preserve the two-stage invalid-calibration history, reject
an invalid packet's range-checked phase, and retain the original—not clamped—
bound in the logical captured state. Actual AIG evaluation separates
packet acceptance, calibration acceptance and their conjunction.

Owned-current controls reject forged partial histories, cross-assignment
tables and vacuous empty-job completion. Microclock controls retain the first
actual gate tick, both final control ticks, explicit rejection and absence of
prefilled output. Physical consumers include mixed commands, exact successful
latency, replacement-initial rejection and no-Zeno continuation.

Actual graph evaluation gives 326,634 ticks for coarse ADC with a three-bit
header. The two materialized comparison banks independently distinguish a
low-energy channel, an accepted channel and an invalid positive-span channel.

Complete code-only execution also checks literal raw-integer packets: all-high
and mixed commands return their independently specified ten bits; bad header,
nonpositive span and unused word code return visible rejection. On the same
all-high probe, the array-ownership repair changed measured host execution from
235,977 ms to 11,404 ms while retaining all 326,634 microsteps. This is a
single-probe runtime measurement, not a complexity theorem or physical clock.

The installed-program regression reuses one coarse/three-bit program across
those five inputs: packet/calibration sizes are 3,201/3,220 and the deadline
remains 326,634. With outputs forced before ending the timer, one host run took
7,940/8,028 ms for the two accepted packets and 149/227/156 ms for the three
rejections; program compilation and materialization took 3 ms. These timings
include output printing. Independent IR/C inspection confirms that the hot
microstep call path contains no packet/calibration compiler or bitblaster;
latched vectors and the safe batch move remain on the actual execution path.

This closes the complete declaration-clocked receiver and its physical delay
composition. The clock counts abstract gate and parallel latch/control
primitives; a transistor propagation bound remains a separate realization.

The [loaded conductance cell](source-generated-conductance-cell.md) now supplies
a source-generated continuous dual-rail realization of the complete original AIG,
including signed loads, all-node restoration and its own physical sampling clock.
The five 128-bit graphs consume it directly; the raw voltage-history compiler
also supports finite stable windows and a complete 128-bit word consumer.
The [whole-receiver graph](source-generated-whole-receiver.md) now compiles the
complete acyclic arithmetic into one shared AIG and reads all eleven outputs
through the actual captured/held bank. Its unconditional equality preserves
the original acceptance and rejection semantics. The installed digital
processing count is not silently replaced by this graph's propagation clock.

## Authority

Below
`SaturationMonoid/NoIslandNoMagic/Consciousness/Immortality/Embodied/Canonical/Coupling/Physical/Netlist/Dissipative/Dimensioned/Driven/`:

- `Commands/Gates/FiniteADC128GateOperations.lean`: fixed graphs and operand-driven reads.
- `Commands/Gates/FiniteADC128GateCorrectness.lean`: bit-for-bit operation correctness.
- `Commands/Gates/Execution/SourceGeneratedAIGExecution.lean`: empty-to-complete cached execution.
- `Commands/Gates/Execution/SourceGeneratedAIGExecutionView.lean`: fixed buffer/cursor carrier and proof-only prefix view.
- `Commands/Gates/Execution/SourceGeneratedAIGExecutionCorrectness.lean`: generated consistency and exact reads.
- `Commands/Gates/Execution/SourceGeneratedAIGVectorExecution.lean`: all word outputs share one table.
- `Commands/Gates/Execution/SourceGeneratedAIGExecutionRegression.lean`: source, completion and reuse controls.
- `Commands/Gates/FiniteADCGateReceiverMachine.lean`: actual arithmetic gate stages.
- `Commands/Gates/FiniteADCGateReceiverMachineCorrectness.lean`: whole-step and iterate exactness.
- `Commands/Gates/Admission/FiniteADCRawPacketAdmission.lean`: raw/decoded semantic bridge.
- `Commands/Gates/Admission/FiniteADCRawAdmissionGate.lean`: source ASTs, assignments and actual graph runs.
- `Commands/Gates/Admission/FiniteADCRawAdmissionGateCorrectness.lean`: exact packet/calibration/admission gates.
- `Commands/Gates/Admission/FiniteADCRawAdmissionGateBoundary.lean`: width, range and span controls.
- `Commands/Clocked/FiniteADCRawReceiverMachine.lean`: raw packet and gate-driven phases.
- `Commands/Clocked/FiniteADCRawReceiverCorrectness.lean`: all-state semiconjugacy and exact output.
- `Commands/Clocked/FiniteADCRawReceiverRegression.lean`: phase order and original metadata.
- `Runtime/Clocked/FiniteADCPhysicalGateReceiver.lean`: actual graph output generates physical next.
- `Runtime/Clocked/FiniteADCPhysicalGateReceiverRegression.lean`: direct consumers and controls.
- `Commands/Gates/Execution/AIGOwnedProgress.lean`, `AIGOwnedBatch.lean`: actual owned progress and parallel cached tables.
- `Commands/Gates/Execution/AIGOwnedFiniteState.lean`: exact finite-cursor classification of stored source histories.
- `Commands/Clocked/Micro/FiniteADCRawPhaseCalls.lean` and `FiniteADCRawPhaseCallsCorrectness.lean`: source calls, materialized registers and exact readouts.
- `Commands/Clocked/Micro/FiniteADCRawInstalledProgram.lean`: source-only installation, stored entrypoint calls and exact reads.
- `Commands/Clocked/Micro/FiniteADCRawMicroMachine.lean`, `FiniteADCRawMicroRank.lean`, `FiniteADCRawMicroCorrectness.lean`, `FiniteADCRawMicroTiming.lean`: actual microsteps, generated deadline, output exactness and successful latency.
- `Runtime/Clocked/FiniteADCPhysicalMicroReceiver.lean` and its regression: micro-output drives the same delayed physical next.
- `Runtime/Clocked/FiniteADCPhysicalMicroInstallation.lean`: source-only boot installation and exact finite bound.
- `Runtime/Clocked/FiniteADCPhysicalInstalledMicroCurrent.lean`: current snapshot, stored program, generated next admission and existing continuation.
- `Runtime/Clocked/FiniteADCPhysicalInstalledMicroRegression.lean`: actual-current and installation controls.
- `Commands/Clocked/Micro/FiniteADCRawMicroExecutableRegression.lean`: independently specified raw inputs and complete accepted/rejected execution.
- `Commands/Clocked/Micro/FiniteADCRawMicroInstalledRegression.lean`: same-program reuse, source/ref replacement rejection and stored-size deadline.
- `Commands/Clocked/Micro/FiniteADCRawMicroFiniteCarrier.lean`: finite whole-state carrier of the actual microengine.

Current responsibility belongs to the [active route](../../handoffs/thick-concept-representation-active-route.md).
