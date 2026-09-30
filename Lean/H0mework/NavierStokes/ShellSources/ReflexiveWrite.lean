import H0mework.Realization.Reflexive.Iteration
import H0mework.NavierStokes.ShellSources.RuntimeDisposition

/-!
# Reflexive execution of the generated integer-shell source

The existing integer-shell responder already owns the only branch:

```text
no active outer nonlinear row
or
least active whole shell → native successor.
```

This module makes that producer operational as one reflexive event.  Its
observation is the complete coefficient receipt written by the current
source response, and is zero exactly when the responder is closed.  The same
event writes the dependent successor.  Hence a nonzero read cannot be
separated from its native update:

```text
read current obstruction
= same event write receipt and next source.
```

Iteration uses the repository's canonical `ReflexiveQuery` execution.  On an
infinite generated lineage, every iterated read is exactly the already
existing nonzero receipt whose squares enter the receipt-square cascade.
There is no caller-supplied shell, branch, path, nonzero witness, cutoff, or
continuation certificate.

The zero branch is faithful for the integer-shell response domain: it means
the complete active outer nonlinear inventory is empty.  It is not, by
itself, a Navier--Stokes regularity or PDE terminal theorem.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellRuntimeDisposition

noncomputable section

/-! ## One source-owned reflexive event -/

/-- Repackage one literal response equality as its exact receipt. -/
def receiptOfResponse
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    GeneratedIntegerShellReceipt where
  current := current
  response := response
  generated := generated

/--
The complete trace observed at the current source.

The zero value is used only when the source-owned responder returns `none`.
Every successful branch emits its already proved nonzero whole-shell trace.
-/
def reflexiveObservation
    (current : RawVorticityFourierSource) :
    IntegerShellCoefficientCarrier :=
  match generatedIntegerShellRespond current with
  | none => 0
  | some response =>
      generatedIntegerShellTrace current response.2.shellSq

/--
The state write performed by the same read event.  Closure is stationary;
a successful response writes its dependent target.
-/
def reflexiveWrite
    (current : RawVorticityFourierSource) :
    RawVorticityFourierSource :=
  match generatedIntegerShellRespond current with
  | none => current
  | some response => response.1

/-- The generated integer-shell source as a state-transforming read. -/
def integerShellReflexiveQuery :
    ReflexiveQuery RawVorticityFourierSource
      IntegerShellCoefficientCarrier where
  read := reflexiveObservation
  write := reflexiveWrite

@[simp] theorem reflexiveObservation_of_none
    (current : RawVorticityFourierSource)
    (stopped :
      generatedIntegerShellRespond current = none) :
    reflexiveObservation current = 0 := by
  unfold reflexiveObservation
  rw [stopped]

@[simp] theorem reflexiveWrite_of_none
    (current : RawVorticityFourierSource)
    (stopped :
      generatedIntegerShellRespond current = none) :
    reflexiveWrite current = current := by
  unfold reflexiveWrite
  rw [stopped]

theorem reflexiveObservation_of_some
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    reflexiveObservation current =
      generatedIntegerShellReceiptTrace
        (receiptOfResponse current response generated) := by
  unfold reflexiveObservation
  rw [generated]
  rfl

theorem reflexiveWrite_of_some
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    reflexiveWrite current = response.1 := by
  unfold reflexiveWrite
  rw [generated]

/--
One successful read and its dependent source write are literally the two
outputs of the same reflexive event.
-/
theorem query_run_of_some
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    ReflexiveQuery.run integerShellReflexiveQuery current =
      (generatedIntegerShellTrace current response.2.shellSq,
        response.1) := by
  simp only [ReflexiveQuery.run, integerShellReflexiveQuery]
  unfold reflexiveObservation reflexiveWrite
  rw [generated]

/-- A stopped read is stationary and emits exactly the zero observation. -/
theorem query_run_of_none
    (current : RawVorticityFourierSource)
    (stopped :
      generatedIntegerShellRespond current = none) :
    ReflexiveQuery.run integerShellReflexiveQuery current =
      (0, current) := by
  simp only [ReflexiveQuery.run, integerShellReflexiveQuery]
  rw [reflexiveObservation_of_none current stopped,
    reflexiveWrite_of_none current stopped]

/-! ## Faithful zero and native write -/

/--
The whole receipt observation is zero exactly on the literal stopped branch.
Successful response traces cannot fall into the observation kernel.
-/
theorem reflexiveObservation_eq_zero_iff
    (current : RawVorticityFourierSource) :
    reflexiveObservation current = 0 ↔
      generatedIntegerShellRespond current = none := by
  cases generated :
      generatedIntegerShellRespond current with
  | none =>
      constructor
      · intro _
        rfl
      · intro _
        exact reflexiveObservation_of_none current generated
  | some response =>
      let receipt :=
        receiptOfResponse current response generated
      have traceNonzero :
          generatedIntegerShellReceiptTrace receipt ≠ 0 :=
        coefficientTrace_ne_zero receipt
      constructor
      · intro observationZero
        have observationEq :
            reflexiveObservation current =
              generatedIntegerShellReceiptTrace receipt := by
          exact
            reflexiveObservation_of_some
              current response generated
        exact False.elim
          (traceNonzero (observationEq.symm.trans observationZero))
      · intro impossible
        exact False.elim
          ((Option.some_ne_none response) impossible)

/--
Zero observation is equivalent to exhaustion of the complete active outer
nonlinear inventory at the same current.
-/
theorem reflexiveObservation_eq_zero_iff_noActiveOuter
    (current : RawVorticityFourierSource) :
    reflexiveObservation current = 0 ↔
      generatedActiveOuterNonlinearModes current = ∅ :=
  (reflexiveObservation_eq_zero_iff current).trans
    (generatedIntegerShellRespond_eq_none_iff current)

/-- Every nonzero observation internally determines a literal native response. -/
theorem exists_response_of_reflexiveObservation_ne_zero
    (current : RawVorticityFourierSource)
    (observationNonzero :
      reflexiveObservation current ≠ 0) :
    ∃ response : Response GeneratedIntegerShellStep current,
      generatedIntegerShellRespond current = some response := by
  cases generated :
      generatedIntegerShellRespond current with
  | none =>
      exact False.elim <|
        observationNonzero
          (reflexiveObservation_of_none current generated)
  | some response =>
      exact ⟨response, rfl⟩

/--
The exact source write-back attached to a successful reflexive event.
-/
theorem receipt_coefficient_writeBack
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    generatedCoefficientCarrier response.1 =
      generatedCoefficientCarrier current +
        generatedIntegerShellReceiptTrace
          (receiptOfResponse current response generated) := by
  exact
    coefficientCarrier_next
      (receiptOfResponse current response generated)

/--
The source current itself generates the only two legal event outcomes:

* a faithful zero read, stationary write, and exhausted outer inventory; or
* a nonzero complete receipt, dependent native successor, and exact
  coefficient write-back.
-/
inductive ReflexiveDisposition
    (current : RawVorticityFourierSource) : Type
  | closed
      (run :
        ReflexiveQuery.run integerShellReflexiveQuery current =
          (0, current))
      (noActiveOuter :
        generatedActiveOuterNonlinearModes current = ∅)
  | native
      (receipt : GeneratedIntegerShellReceipt)
      (currentEq : receipt.current = current)
      (run :
        ReflexiveQuery.run integerShellReflexiveQuery current =
          (generatedIntegerShellReceiptTrace receipt, receipt.next))
      (traceNonzero :
        generatedIntegerShellReceiptTrace receipt ≠ 0)
      (writeBack :
        generatedCoefficientCarrier receipt.next =
          generatedCoefficientCarrier receipt.current +
            generatedIntegerShellReceiptTrace receipt)

/-- Generate the zero-or-native disposition without an input branch. -/
noncomputable def generatedReflexiveDisposition
    (current : RawVorticityFourierSource) :
    ReflexiveDisposition current := by
  cases generated :
      generatedIntegerShellRespond current with
  | none =>
      exact .closed
        (query_run_of_none current generated)
        ((generatedIntegerShellRespond_eq_none_iff current).mp
          generated)
  | some response =>
      let receipt :=
        receiptOfResponse current response generated
      exact .native receipt rfl
        (by
          simpa [receipt, receiptOfResponse,
            generatedIntegerShellReceiptTrace,
            GeneratedIntegerShellReceipt.selectedShellSq] using
            query_run_of_some current response generated)
        (coefficientTrace_ne_zero receipt)
        (coefficientCarrier_next receipt)

/-! ## Recursive write chain and receipt-square lineage -/

namespace ReflexiveLineage

/--
At every source-generated lineage occurrence, the reflexive read emits
exactly that occurrence's receipt and writes exactly the next lineage state.
-/
theorem query_run_receipt
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    ReflexiveQuery.run integerShellReflexiveQuery
        (lineage.current index) =
      (generatedIntegerShellReceiptTrace (lineage.receipt index),
        lineage.current (index + 1)) := by
  simpa [GeneratedIntegerShellInfiniteLineage.receipt,
    GeneratedIntegerShellInfiniteLineage.response,
    generatedIntegerShellReceiptTrace,
    GeneratedIntegerShellReceipt.selectedShellSq] using
    query_run_of_some
      (lineage.current index)
      (lineage.response index)
      (lineage.response_generated index)

/-- Every read on an actual infinite write chain is nonzero. -/
theorem reflexiveObservation_ne_zero
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    reflexiveObservation (lineage.current index) ≠ 0 := by
  rw [reflexiveObservation_of_some
    (lineage.current index)
    (lineage.response index)
    (lineage.response_generated index)]
  exact coefficientTrace_ne_zero (lineage.receipt index)

/--
The same event's observed trace is the positive quantum already consumed by
the receipt-square cascade.
-/
theorem observedTrace_normSq_eq_receiptQuantum
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    coefficientCarrierNormSq
        (reflexiveObservation (lineage.current index)) =
      lineage.receiptQuantum index := by
  rw [reflexiveObservation_of_some
    (lineage.current index)
    (lineage.response index)
    (lineage.response_generated index)]
  rfl

/-- The iterated reflexive write reaches exactly the source lineage state. -/
theorem iterated_stateAt_eq_current
    (lineage : GeneratedIntegerShellInfiniteLineage) :
    ∀ index : ℕ,
      (reflexiveQueryIteratedTimeField integerShellReflexiveQuery
        (lineage.current 0)).stateAt index =
          lineage.current index
  | 0 => rfl
  | index + 1 => by
      rw [reflexiveQueryIterated_stateAt_succ]
      rw [iterated_stateAt_eq_current lineage index]
      have run := query_run_receipt lineage index
      exact congrArg Prod.snd run

/--
The canonical repeated query execution is therefore the actual generated
scale path, rather than an independently supplied horizon receipt.
-/
theorem repeatEval_canonical
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ) :
    StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive integerShellReflexiveQuery)
        (reflexiveQueryStatefulPlan integerShellReflexiveQuery)
        length
        (lineage.current 0)
        (reflexiveQueryIteratedObservationTrace
          integerShellReflexiveQuery
          (lineage.current 0) length)
        (lineage.current length) := by
  have canonical :=
    reflexiveStatefulPlan_repeatEval_canonical
      integerShellReflexiveQuery (lineage.current 0) length
  rw [iterated_stateAt_eq_current lineage length] at canonical
  exact canonical

/--
The squared mass of the first `length` reflexive observations is exactly the
existing prefix receipt-square mass.
-/
theorem prefixReceiptTraceSquareMass_eq_reflexiveObservations
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ) :
    lineage.prefixReceiptTraceSquareMass length =
      ∑ index ∈ Finset.range length,
        coefficientCarrierNormSq
          (reflexiveObservation (lineage.current index)) ^ 2 := by
  rw [lineage.prefixReceiptTraceSquareMass_eq_sum_range length]
  apply Finset.sum_congr rfl
  intro index indexMem
  rw [observedTrace_normSq_eq_receiptQuantum lineage index]

end ReflexiveLineage

/-! ## Maximal source execution in reflexive form -/

/--
The existing maximal runtime now has exactly the reflexive meaning required
by the source grammar: it reaches a faithful zero read, or it is an infinite
chain of nonzero reads whose same events write the next native states.
-/
inductive ReflexiveRuntimeDisposition
    (seed : RawVorticityFourierSource) : Type
  | closed
      (run : GeneratedIntegerShellTerminalRun seed)
      (queryRun :
        ReflexiveQuery.run integerShellReflexiveQuery run.terminal =
          (0, run.terminal))
      (noActiveOuter :
        generatedActiveOuterNonlinearModes run.terminal = ∅)
  | infinite
      (lineage : GeneratedIntegerShellInfiniteLineage)
      (startsAtSeed : lineage.current 0 = seed)
      (queryRun :
        ∀ index : ℕ,
          ReflexiveQuery.run integerShellReflexiveQuery
              (lineage.current index) =
            (generatedIntegerShellReceiptTrace
                (lineage.receipt index),
              lineage.current (index + 1)))
      (readNonzero :
        ∀ index : ℕ,
          reflexiveObservation (lineage.current index) ≠ 0)

/-- Generate the maximal reflexive runtime directly from the literal seed. -/
noncomputable def generatedReflexiveRuntimeDisposition
    (seed : RawVorticityFourierSource) :
    ReflexiveRuntimeDisposition seed := by
  cases generatedIntegerShellRuntimeDisposition seed with
  | terminal run =>
      exact .closed run
        (query_run_of_none run.terminal run.stopped)
        run.noActiveOuterNonlinearModes
  | infinite lineage startsAtSeed =>
      exact .infinite lineage startsAtSeed
        (ReflexiveLineage.query_run_receipt lineage)
        (ReflexiveLineage.reflexiveObservation_ne_zero lineage)

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite
end NavierStokes
end SaturationMonoid
