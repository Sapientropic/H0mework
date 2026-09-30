import H0mework.Realization.Reflexive.StatefulRead
import H0mework.NavierStokes.PairRestart.PairDuhamelTerminalTraceRedirect
import H0mework.NavierStokes.PairRestart.PairDuhamelKineticTriadRedirect
import H0mework.NavierStokes.VelocityEndpoint.AlignedResponsibilityProcess

/-!
# Cofinal causal-commutator lineage at a bounded whole-restart endpoint

Finite accumulation already generates a nonzero causal pair responsibility
arbitrarily far along the actual whole-restart run.  On that identical
receipt, the native reflected velocity relation closes after causal heat
transport only up to its exact heat-commutator trace.

This module makes those facts one source-owned recursive lineage.  Each event
is selected after both the preceding event and the next canonical endpoint
occurrence.  Consequently its indices are strictly increasing, its physical
times converge to the same generated accumulation endpoint, and consecutive
events are joined by a nonempty path of the existing native unforced update.

The event ledger records the pre-quotient pair responsibility and its exact
causal commutator before any scalar quotient.  A vanishing commutator means
the reflected work relation closes on that receipt; it does not erase the
independently generated next-pair/trace responsibility.  No output, pair,
path, branch, cutoff, target state, continuation witness, nonzero charge or
faithfulness law is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCofinalPairCausalCommutatorLineage

open scoped BigOperators ENNReal Interval

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationRateObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open AffineRelaxation

noncomputable section

/-! ## One source-selected late relation event -/

/-- One actual causal pair responsibility selected after a requested native
index.  The requested index is recorded as provenance, but the output, pair
and next/trace disposition are generated internally. -/
structure GeneratedWholeRestartCofinalPairCausalCommutatorReceipt where
  requestedStart : ℕ
  eventIndex : ℕ
  output : IntegerWavevector
  first : IntegerWavevector

private theorem elapsedTime_bddAbove_exists_arbitrarily_late_pairDuhamelOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requestedStart : ℕ) :
    ∃ index : ℕ,
      requestedStart ≤ index ∧
        ∃ output : IntegerWavevector,
          output ≠ 0 ∧
            ∃ first : IntegerWavevector,
              wholeRestartPairDuhamelOccurrence
                initial index output first ≠ 0 := by
  have rateNotSummable :=
    elapsedTime_bddAbove_forces_nonlinearRegenerationRateSquare_not_summable
      initial elapsedBounded
  have existsRate :
      ∃ index : ℕ,
        requestedStart ≤ index ∧
          wholeRestartNonlinearRegenerationRateSquare
            initial index ≠ 0 := by
    by_contra noRate
    push Not at noRate
    have tailZero :
        (fun offset : ℕ =>
          wholeRestartNonlinearRegenerationRateSquare
            initial (offset + requestedStart)) = 0 := by
      funext offset
      exact noRate (offset + requestedStart) (by omega)
    have tailSummable :
        Summable fun offset : ℕ =>
          wholeRestartNonlinearRegenerationRateSquare
            initial (offset + requestedStart) := by
      rw [tailZero]
      exact summable_zero
    apply rateNotSummable
    exact
      (summable_nat_add_iff
        (G := ℝ)
        (f := wholeRestartNonlinearRegenerationRateSquare initial)
        requestedStart).mp tailSummable
  obtain ⟨index, startLe, rateNonzero⟩ := existsRate
  have regenerationStateNonzero :
      wholeRestartNonlinearRegenerationState initial index ≠ 0 := by
    intro regenerationStateZero
    apply rateNonzero
    simp [wholeRestartNonlinearRegenerationRateSquare,
      wholeRestartNonlinearRegenerationNorm, regenerationStateZero]
  have existsOutput :
      ∃ output : IntegerWavevector,
        wholeRestartNonlinearRegenerationState
          initial index output ≠ 0 := by
    by_contra noOutput
    push Not at noOutput
    apply regenerationStateNonzero
    apply lp.ext
    funext output
    exact noOutput output
  obtain ⟨output, outputRowNonzero⟩ := existsOutput
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    exact outputRowNonzero
      (wholeRestartNonlinearRegenerationState_zero initial index)
  have aggregateNonzero :
      (∑' first : IntegerWavevector,
        wholeRestartPairDuhamelOccurrence
          initial index output first) ≠ 0 := by
    rw [tsum_wholeRestartPairDuhamelOccurrence_eq_regeneration
      initial index output outputNonzero]
    exact outputRowNonzero
  have existsFirst :
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelOccurrence
          initial index output first ≠ 0 := by
    by_contra noFirst
    push Not at noFirst
    apply aggregateNonzero
    have tableZero :
        (fun first : IntegerWavevector =>
          wholeRestartPairDuhamelOccurrence
            initial index output first) = 0 := by
      funext first
      exact noFirst first
    rw [tableZero]
    exact tsum_zero
  exact ⟨index, startLe, output, outputNonzero, existsFirst⟩

private theorem exists_generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requestedStart : ℕ) :
    ∃ receipt : GeneratedWholeRestartCofinalPairCausalCommutatorReceipt,
      receipt.requestedStart = requestedStart ∧
      requestedStart ≤ receipt.eventIndex ∧
      receipt.output ≠ 0 ∧
      wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
        receipt.output receipt.first ≠ 0 := by
  let existsIndex :=
    elapsedTime_bddAbove_exists_arbitrarily_late_pairDuhamelOccurrence
      initial elapsedBounded requestedStart
  let index := Classical.choose existsIndex
  have indexSpec := Classical.choose_spec existsIndex
  let output := Classical.choose indexSpec.2
  have outputSpec := Classical.choose_spec indexSpec.2
  let first := Classical.choose outputSpec.2
  have firstSpec := Classical.choose_spec outputSpec.2
  exact
    ⟨{
      requestedStart := requestedStart
      eventIndex := index
      output := output
      first := first
    }, rfl, indexSpec.1, outputSpec.1, firstSpec⟩

/-- Finite accumulation itself chooses the first actual relation event at or
after `requestedStart`. -/
noncomputable def generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requestedStart : ℕ) :
    GeneratedWholeRestartCofinalPairCausalCommutatorReceipt :=
  Classical.choose
    (exists_generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
      initial elapsedBounded requestedStart)

@[simp] theorem
    generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter_requestedStart
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requestedStart : ℕ) :
    (generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
      initial elapsedBounded requestedStart).requestedStart =
      requestedStart :=
  (Classical.choose_spec
    (exists_generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
      initial elapsedBounded requestedStart)).1

theorem generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter_start_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requestedStart : ℕ) :
    requestedStart ≤
      (generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
        initial elapsedBounded requestedStart).eventIndex :=
  (Classical.choose_spec
    (exists_generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
      initial elapsedBounded requestedStart)).2.1

theorem generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter_output_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requestedStart : ℕ) :
    (generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
      initial elapsedBounded requestedStart).output ≠ 0 :=
  (Classical.choose_spec
    (exists_generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
      initial elapsedBounded requestedStart)).2.2.1

theorem generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter_pairDuhamel_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requestedStart : ℕ) :
    let receipt :=
      generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
        initial elapsedBounded requestedStart
    wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
      receipt.output receipt.first ≠ 0 :=
  (Classical.choose_spec
    (exists_generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
      initial elapsedBounded requestedStart)).2.2.2

namespace GeneratedWholeRestartCofinalPairCausalCommutatorReceipt

/-- The second input is forced by the selected output incidence. -/
def second
    (receipt : GeneratedWholeRestartCofinalPairCausalCommutatorReceipt) :
    IntegerWavevector :=
  receipt.output - receipt.first

theorem first_add_second
    (receipt : GeneratedWholeRestartCofinalPairCausalCommutatorReceipt) :
    receipt.first + receipt.second = receipt.output := by
  unfold second
  abel

/-- The nonzero selected pair independently generates its actual next-pair
keep or same-receipt causal trace. -/
theorem nativeResponsibility
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (receipt : GeneratedWholeRestartCofinalPairCausalCommutatorReceipt)
    (pairNonzero :
      wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
        receipt.output receipt.first ≠ 0) :
    wholeRestartNextPairOccurrence initial receipt.eventIndex
          receipt.output receipt.first ≠ 0 ∨
      wholeRestartPairDuhamelCausalTrace initial receipt.eventIndex
        receipt.output receipt.first ≠ 0 := by
  exact
    wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
      initial receipt.eventIndex receipt.output receipt.first
      pairNonzero

/-- The same selected pair and its swapped companion compile back to the
physical curl before the output quotient. -/
theorem pairDuhamel_add_swap_eq_velocityPair_curl
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (receipt : GeneratedWholeRestartCofinalPairCausalCommutatorReceipt) :
    wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
          receipt.output receipt.first +
        wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
          receipt.output receipt.second =
      fourierCurlCoefficient receipt.output
        (wholeRestartSymmetricVelocityPairDuhamelOccurrence
          initial receipt.eventIndex receipt.first receipt.second) := by
  simpa only [second] using
    wholeRestartPairDuhamelOccurrence_add_swap_eq_velocityPair_curl
      initial receipt.eventIndex receipt.output receipt.first

/-- The causal observer has no silent branch.  A nonzero commutator remains
visible.  If it vanishes, the reflected work relation closes exactly while
the original nonzero pair responsibility still enters its independently
generated next-pair or whole-trace disposition. -/
theorem causalCommutator_ne_zero_or_reflectedClosure_and_nativeResponsibility
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (receipt : GeneratedWholeRestartCofinalPairCausalCommutatorReceipt)
    (pairNonzero :
      wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
        receipt.output receipt.first ≠ 0) :
    wholeRestartVelocityTriadHeatCommutatorTrace
          initial receipt.eventIndex receipt.first receipt.second ≠ 0 ∨
      (wholeRestartVelocityTriadHeatCommutatorTrace
            initial receipt.eventIndex receipt.first receipt.second = 0 ∧
        (wholeRestartNextPairOccurrence initial receipt.eventIndex
              receipt.output receipt.first ≠ 0 ∨
          wholeRestartPairDuhamelCausalTrace
            initial receipt.eventIndex receipt.output receipt.first ≠ 0)) := by
  by_cases commutatorNonzero :
      wholeRestartVelocityTriadHeatCommutatorTrace
        initial receipt.eventIndex receipt.first receipt.second ≠ 0
  · exact Or.inl commutatorNonzero
  · right
    constructor
    · exact not_ne_iff.mp commutatorNonzero
    · exact receipt.nativeResponsibility pairNonzero

end GeneratedWholeRestartCofinalPairCausalCommutatorReceipt

open GeneratedWholeRestartCofinalPairCausalCommutatorReceipt

/-! ## Recursive endpoint-aligned source lineage -/

/-- The first relation event is requested after the first canonical endpoint
occurrence.  Every later request lies after both the previous selected event
and the next canonical endpoint occurrence. -/
noncomputable def generatedWholeRestartCofinalPairCausalCommutatorStart
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ℕ → ℕ
  | 0 =>
      wholeRestartEndpointSelectedOccurrenceIndex
        initial elapsedBounded 0
  | index + 1 =>
      max
        ((generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
            initial elapsedBounded
            (generatedWholeRestartCofinalPairCausalCommutatorStart
              initial elapsedBounded index)).eventIndex + 1)
        (wholeRestartEndpointSelectedOccurrenceIndex
          initial elapsedBounded (index + 1))

/-- The complete source-generated cofinal relation event at lineage index
`index`. -/
noncomputable def generatedWholeRestartCofinalPairCausalCommutatorReceipt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    GeneratedWholeRestartCofinalPairCausalCommutatorReceipt :=
  generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter
    initial elapsedBounded
    (generatedWholeRestartCofinalPairCausalCommutatorStart
      initial elapsedBounded index)

/-- Actual native index carrying one generated relation event. -/
def generatedWholeRestartCofinalPairCausalCommutatorIndex
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : ℕ :=
  (generatedWholeRestartCofinalPairCausalCommutatorReceipt
    initial elapsedBounded index).eventIndex

theorem generatedWholeRestartCofinalPairCausalCommutatorIndex_ge_endpoint
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartEndpointSelectedOccurrenceIndex
        initial elapsedBounded index ≤
      generatedWholeRestartCofinalPairCausalCommutatorIndex
        initial elapsedBounded index := by
  have startLe :
      wholeRestartEndpointSelectedOccurrenceIndex
          initial elapsedBounded index ≤
        generatedWholeRestartCofinalPairCausalCommutatorStart
          initial elapsedBounded index := by
    cases index with
    | zero => rfl
    | succ index =>
        exact le_max_right _ _
  have generatedLe :=
    generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter_start_le
      initial elapsedBounded
      (generatedWholeRestartCofinalPairCausalCommutatorStart
        initial elapsedBounded index)
  exact startLe.trans generatedLe

/-- Consecutive source-generated relation events are strictly ordered in the
authoritative native run. -/
theorem generatedWholeRestartCofinalPairCausalCommutatorIndex_lt_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    generatedWholeRestartCofinalPairCausalCommutatorIndex
        initial elapsedBounded index <
      generatedWholeRestartCofinalPairCausalCommutatorIndex
        initial elapsedBounded (index + 1) := by
  have nextStartLe :
      generatedWholeRestartCofinalPairCausalCommutatorIndex
            initial elapsedBounded index + 1 ≤
        generatedWholeRestartCofinalPairCausalCommutatorStart
          initial elapsedBounded (index + 1) := by
    exact le_max_left _ _
  have generatedLe :=
    generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter_start_le
      initial elapsedBounded
      (generatedWholeRestartCofinalPairCausalCommutatorStart
        initial elapsedBounded (index + 1))
  exact (Nat.lt_succ_self _).trans_le (nextStartLe.trans generatedLe)

theorem generatedWholeRestartCofinalPairCausalCommutatorIndex_strictMono
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    StrictMono
      (generatedWholeRestartCofinalPairCausalCommutatorIndex
        initial elapsedBounded) := by
  apply strictMono_nat_of_lt_succ
  exact
    generatedWholeRestartCofinalPairCausalCommutatorIndex_lt_succ
      initial elapsedBounded

/-- The generated relation lineage reaches the same finite accumulation
endpoint as the canonical source-owned velocity subsequence. -/
theorem generatedWholeRestartCofinalPairCausalCommutatorTime_tendsto_endpoint
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun index =>
        elapsedTime initial
          (generatedWholeRestartCofinalPairCausalCommutatorIndex
            initial elapsedBounded index))
      atTop
      (nhds (wholeRestartVelocityAccumulationTime initial)) := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).family.endpointReceipt
  have lowerTendsto :
      Tendsto
        (fun index => elapsedTime initial
          (wholeRestartEndpointSelectedOccurrenceIndex
            initial elapsedBounded index))
        atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) := by
    simpa only [wholeRestartEndpointSelectedOccurrenceIndex,
      endpointReceipt] using endpointReceipt.elapsed_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    lowerTendsto tendsto_const_nhds ?_ ?_
  · exact Eventually.of_forall fun index =>
      (elapsedTime_strictMono initial).monotone
        (generatedWholeRestartCofinalPairCausalCommutatorIndex_ge_endpoint
          initial elapsedBounded index)
  · exact Eventually.of_forall fun index => by
      unfold wholeRestartVelocityAccumulationTime
      exact le_ciSup elapsedBounded
        (generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded index)

/-! ## Actual path and reflexive write ledger -/

/-- Number of literal native updates between adjacent generated relation
events. -/
def generatedWholeRestartCofinalPairCausalCommutatorGap
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : ℕ :=
  generatedWholeRestartCofinalPairCausalCommutatorIndex
      initial elapsedBounded (index + 1) -
    generatedWholeRestartCofinalPairCausalCommutatorIndex
      initial elapsedBounded index

theorem generatedWholeRestartCofinalPairCausalCommutatorGap_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    0 < generatedWholeRestartCofinalPairCausalCommutatorGap
      initial elapsedBounded index := by
  have strict :=
    generatedWholeRestartCofinalPairCausalCommutatorIndex_lt_succ
      initial elapsedBounded index
  unfold generatedWholeRestartCofinalPairCausalCommutatorGap
  omega

/-- Adjacent relation events are joined by the exact nonempty path of the
existing source-owned unforced `.next` update. -/
theorem generatedWholeRestartCofinalPairCausalCommutator_nativeGapPath
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    run initial
        (generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (index + 1)) =
      (GeneratedWholeRestartCurrent.next^[
        generatedWholeRestartCofinalPairCausalCommutatorGap
          initial elapsedBounded index])
        (run initial
          (generatedWholeRestartCofinalPairCausalCommutatorIndex
            initial elapsedBounded index)) := by
  have strict :=
    generatedWholeRestartCofinalPairCausalCommutatorIndex_lt_succ
      initial elapsedBounded index
  rw [← wholeRestart_run_add_eq_iterate_next]
  congr 1
  unfold generatedWholeRestartCofinalPairCausalCommutatorGap
  omega

/-- Reading one generated relation event writes the next event position.
The physical meaning of that write is the native gap path above. -/
def generatedWholeRestartCofinalPairCausalCommutatorQuery
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ReflexiveQuery ℕ
      GeneratedWholeRestartCofinalPairCausalCommutatorReceipt where
  read := generatedWholeRestartCofinalPairCausalCommutatorReceipt
    initial elapsedBounded
  write := Nat.succ

@[simp] theorem generatedWholeRestartCofinalPairCausalCommutatorQuery_run
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    (generatedWholeRestartCofinalPairCausalCommutatorQuery
      initial elapsedBounded).run index =
      (generatedWholeRestartCofinalPairCausalCommutatorReceipt
          initial elapsedBounded index,
        index + 1) := by
  rfl

/-- Chronological pre-quotient ledger written by the generated relation
lineage.  Newest receipt comes first. -/
def generatedWholeRestartCofinalPairCausalCommutatorLedger
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ) :
    List GeneratedWholeRestartCofinalPairCausalCommutatorReceipt :=
  (List.range length).reverse.map
    (generatedWholeRestartCofinalPairCausalCommutatorReceipt
      initial elapsedBounded)

/-- One reflexive read/write event writes exactly its generated receipt into
the lineage ledger. -/
theorem generatedWholeRestartCofinalPairCausalCommutatorLedger_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ) :
    generatedWholeRestartCofinalPairCausalCommutatorLedger
        initial elapsedBounded (length + 1) =
      generatedWholeRestartCofinalPairCausalCommutatorReceipt
          initial elapsedBounded length ::
        generatedWholeRestartCofinalPairCausalCommutatorLedger
          initial elapsedBounded length := by
  simp [generatedWholeRestartCofinalPairCausalCommutatorLedger,
    List.range_succ]

/-- Every event of the endpoint-cofinal ledger retains both its nonzero pair
responsibility and the exact causal observer exhaustion. -/
theorem generatedWholeRestartCofinalPairCausalCommutatorLineage_noSilentLoss
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    let receipt :=
      generatedWholeRestartCofinalPairCausalCommutatorReceipt
        initial elapsedBounded index
    wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
          receipt.output receipt.first ≠ 0 ∧
      (wholeRestartVelocityTriadHeatCommutatorTrace
            initial receipt.eventIndex receipt.first receipt.second ≠ 0 ∨
        (wholeRestartVelocityTriadHeatCommutatorTrace
              initial receipt.eventIndex receipt.first receipt.second = 0 ∧
          (wholeRestartNextPairOccurrence initial receipt.eventIndex
                receipt.output receipt.first ≠ 0 ∨
            wholeRestartPairDuhamelCausalTrace
              initial receipt.eventIndex receipt.output receipt.first ≠ 0))) := by
  dsimp only
  let receipt :=
    generatedWholeRestartCofinalPairCausalCommutatorReceipt
      initial elapsedBounded index
  have pairNonzero :
      wholeRestartPairDuhamelOccurrence initial receipt.eventIndex
        receipt.output receipt.first ≠ 0 := by
    simpa only [receipt,
      generatedWholeRestartCofinalPairCausalCommutatorReceipt] using
      generatedWholeRestartCofinalPairCausalCommutatorReceiptAfter_pairDuhamel_ne_zero
        initial elapsedBounded
        (generatedWholeRestartCofinalPairCausalCommutatorStart
          initial elapsedBounded index)
  exact
    ⟨pairNonzero,
      receipt.causalCommutator_ne_zero_or_reflectedClosure_and_nativeResponsibility
        pairNonzero⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCofinalPairCausalCommutatorLineage
end NavierStokes
end SaturationMonoid
