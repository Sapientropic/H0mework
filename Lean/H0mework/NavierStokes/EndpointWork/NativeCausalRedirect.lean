import H0mework.NavierStokes.VelocityEndpoint.MacroKineticEnergyAtom
import H0mework.NavierStokes.PairRestart.PairDuhamelTangentInnovation

/-!
# A positive endpoint kinetic atom generates an actual native causal redirect

The endpoint kinetic atom was already identified with the limiting square
mass of the complete selected-contact residual.  This module consumes that
whole-carrier fact before any finite Fourier quotient.

A positive atom prevents the selected residual tail from becoming stationary:
the residual is weakly null, while its square norm tends to the positive
atom.  Hence, after every requested native index, two source-selected actual
contacts differ.  The exact finite native path between them must contain one
literal unforced `.next` edge whose physical state changes on a nonzero
Fourier row.

On that same edge and output, the existing causal compiler gives

```text
actual native increment
  = causal gain * source tangent
    + complete pre-quotient pair innovation.
```

If the tangent is zero, one concrete pair innovation is nonzero and enters
its already generated next-pair or same-receipt trace disposition.  Thus a
positive endpoint atom is no longer only a nonzero ledger readout: it
cofinally generates an actual source update carrying a causal tangent or
pair-level native responsibility.

No native edge, output, pair, branch, cutoff, target state, continuation
witness, nonzero witness, or faithfulness certificate is supplied by a
caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomNativeCausalRedirect

open Filter Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation

noncomputable section

/-! ## Weakly-null positive residuals cannot become stationary -/

/-- A nonzero selected endpoint residual forces a later source-selected
physical contact to differ.  Otherwise the residual would be eventually
constant, contradicting its weak convergence to zero. -/
theorem
    wholeRestartKineticEndpointResidual_ne_zero_generates_futureSelectedChange
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ)
    (residualNonzero :
      wholeRestartKineticEndpointResidual initial receipt index ≠ 0) :
    ∃ later : ℕ,
      index < later ∧
        (wholeRestartKineticEndpointSelectedCurrent
            initial receipt later).contact.physicalState ≠
          (wholeRestartKineticEndpointSelectedCurrent
            initial receipt index).contact.physicalState := by
  by_contra noLater
  have futurePhysicalEq :
      ∀ later : ℕ, index < later →
        (wholeRestartKineticEndpointSelectedCurrent
            initial receipt later).contact.physicalState =
          (wholeRestartKineticEndpointSelectedCurrent
            initial receipt index).contact.physicalState := by
    intro later indexLtLater
    by_contra physicalNe
    exact noLater ⟨later, indexLtLater, physicalNe⟩
  let residual :=
    wholeRestartKineticEndpointResidual initial receipt index
  have residualEventuallyEq :
      (fun later =>
        inner ℂ
          (wholeRestartKineticEndpointResidual initial receipt later)
          residual) =ᶠ[atTop]
        (fun _ => inner ℂ residual residual) := by
    filter_upwards [eventually_ge_atTop (index + 1)] with later laterGe
    have indexLtLater : index < later := by omega
    have stateEq := futurePhysicalEq later indexLtLater
    change
      inner ℂ
        (puncturedWholeVorticityKineticEuclideanState
            (wholeRestartKineticEndpointSelectedCurrent
              initial receipt later).contact.physicalState -
          receipt.endpoint)
        residual =
      inner ℂ residual residual
    rw [stateEq]
    rfl
  have weakTendsto :
      Tendsto
        (fun later =>
          inner ℂ
            (wholeRestartKineticEndpointResidual
              initial receipt later)
            residual)
        atTop (nhds 0) :=
    wholeRestartKineticEndpointResidual_weak_tendsto_zero
      receipt residual
  have constantTendsto :
      Tendsto
        (fun later =>
          inner ℂ
            (wholeRestartKineticEndpointResidual
              initial receipt later)
            residual)
        atTop (nhds (inner ℂ residual residual)) :=
    Filter.Tendsto.congr'
      residualEventuallyEq.symm tendsto_const_nhds
  have innerZero :
      (0 : ℂ) = inner ℂ residual residual :=
    tendsto_nhds_unique weakTendsto constantTendsto
  apply residualNonzero
  exact
    (inner_self_eq_zero.mp innerZero.symm)

/-! ## A changed finite path contains a changed literal native edge -/

private theorem sequence_eq_add_of_adjacent_eq
    {α : Type*}
    (sequence : ℕ → α)
    (first : ℕ) :
    ∀ distance : ℕ,
      (∀ index : ℕ,
        first ≤ index → index < first + distance →
          sequence index = sequence (index + 1)) →
        sequence first = sequence (first + distance) := by
  intro distance
  induction distance with
  | zero =>
      intro _adjacentEq
      rfl
  | succ distance inductionHypothesis =>
      intro adjacentEq
      have prefixEq :
          sequence first = sequence (first + distance) :=
        inductionHypothesis fun index firstLe indexLt =>
          adjacentEq index firstLe (by omega)
      exact prefixEq.trans
        (adjacentEq
          (first + distance)
          (Nat.le_add_right first distance)
          (by omega))

theorem exists_adjacent_native_change_of_endpoint_change
    {α : Type*}
    (sequence : ℕ → α)
    {first last : ℕ}
    (firstLtLast : first < last)
    (endpointNe : sequence first ≠ sequence last) :
    ∃ index : ℕ,
      first ≤ index ∧ index < last ∧
        sequence index ≠ sequence (index + 1) := by
  by_cases existsChange :
      ∃ index : ℕ,
        first ≤ index ∧ index < last ∧
          sequence index ≠ sequence (index + 1)
  · exact existsChange
  · exfalso
    apply endpointNe
    have adjacentEq :
        ∀ index : ℕ, first ≤ index → index < last →
          sequence index = sequence (index + 1) := by
      intro index firstLe indexLt
      by_contra change
      exact existsChange ⟨index, firstLe, indexLt, change⟩
    obtain ⟨distance, lastEq⟩ :=
      Nat.exists_eq_add_of_le firstLtLast.le
    subst last
    exact
      sequence_eq_add_of_adjacent_eq
        sequence first distance adjacentEq

/-- A positive endpoint atom generates a changed literal native physical
edge after every requested old-run index.  Both endpoints used to locate the
edge are selected by the canonical weak endpoint receipt. -/
theorem physicalStageKineticEnergyAtom_pos_generates_late_nativeChange
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ index : ℕ,
      requestedStart ≤ index ∧
        (run current index).nextContact.physicalState ≠
          (run current index).contact.physicalState := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  let receipt :=
    endpointReceipt.kineticReceipt.toGeneratedWholeRestartKineticWeakEndpoint
  have defectPositive :
      0 < wholeRestartKineticWeakEndpointDefect
        current receipt.endpoint := by
    rw [← step.physicalStageKineticEnergyAtom_eq_defect]
    exact atomPositive
  have eventuallyResidualPositive :=
    wholeRestartKineticEndpointResidual_eventually_gt_half_defect
      receipt defectPositive
  obtain ⟨threshold, residualPositive⟩ :=
    eventually_atTop.1 eventuallyResidualPositive
  let selectedIndex := max requestedStart threshold
  have selectedIndexGeThreshold : threshold ≤ selectedIndex :=
    Nat.le_max_right _ _
  have selectedNativeGeRequested :
      requestedStart ≤ receipt.subsequence selectedIndex := by
    exact
      (Nat.le_max_left _ _).trans
        (receipt.subsequence_strictMono.id_le selectedIndex)
  have selectedResidualPositive :
      wholeRestartKineticWeakEndpointDefect current receipt.endpoint / 2 <
        ‖wholeRestartKineticEndpointResidual
          current receipt selectedIndex‖ ^ 2 :=
    residualPositive selectedIndex selectedIndexGeThreshold
  have selectedResidualNonzero :
      wholeRestartKineticEndpointResidual
        current receipt selectedIndex ≠ 0 := by
    intro residualZero
    rw [residualZero, norm_zero, pow_two, zero_mul] at selectedResidualPositive
    linarith
  obtain ⟨later, selectedIndexLtLater, selectedPhysicalNe⟩ :=
    wholeRestartKineticEndpointResidual_ne_zero_generates_futureSelectedChange
      receipt selectedIndex selectedResidualNonzero
  have nativeFirstLtLast :
      receipt.subsequence selectedIndex <
        receipt.subsequence later :=
    receipt.subsequence_strictMono selectedIndexLtLater
  obtain ⟨index, firstLeIndex, indexLtLast, adjacentNe⟩ :=
    exists_adjacent_native_change_of_endpoint_change
      (fun native =>
        (run current native).contact.physicalState)
      nativeFirstLtLast selectedPhysicalNe.symm
  refine ⟨index, selectedNativeGeRequested.trans firstLeIndex, ?_⟩
  intro nextEq
  apply adjacentNe
  rw [run_succ]
  exact nextEq.symm

/-! ## Same-edge causal tangent / pair disposition -/

private theorem exists_output_change_of_state_change
    {left right : ComplexVorticityHilbertState}
    (stateNe : left ≠ right) :
    ∃ output : IntegerWavevector, left output ≠ right output := by
  by_contra noOutput
  push Not at noOutput
  apply stateNe
  apply Subtype.ext
  funext output
  exact noOutput output

private theorem exists_pairInnovation_ne_zero_of_tsum_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (aggregateNonzero :
      (∑' first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first) ≠ 0) :
    ∃ first : IntegerWavevector,
      wholeRestartPairDuhamelInnovationOccurrence
        initial index output first ≠ 0 := by
  by_contra noOccurrence
  push Not at noOccurrence
  apply aggregateNonzero
  have tableZero :
      (fun first : IntegerWavevector =>
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first) = 0 := by
    funext first
    exact noOccurrence first
  rw [tableZero]
  exact tsum_zero

/-- The changed native edge has a nonzero Fourier output.  At that exact
output the unforced increment is compiled into its causal tangent plus the
complete pair innovation.  If the tangent vanishes, a concrete innovation
occurrence enters its native next-pair or same-receipt pointwise trace
disposition. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_late_nativeCausalSplit
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ index : ℕ,
      requestedStart ≤ index ∧
        ∃ output : IntegerWavevector,
          output ≠ 0 ∧
          (run current index).nextContact.physicalState output -
              (run current index).contact.physicalState output ≠ 0 ∧
          (run current index).nextContact.physicalState output -
                (run current index).contact.physicalState output =
              wholeRestartCausalTangentGain current index output •
                  wholeRestartCrossingUnforcedTangentRow
                    current index output +
                (∑' first : IntegerWavevector,
                  wholeRestartPairDuhamelInnovationOccurrence
                    current index output first) := by
  obtain ⟨index, requestedLe, stateNe⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_late_nativeChange
      step atomPositive requestedStart
  obtain ⟨output, outputRowNe⟩ :=
    exists_output_change_of_state_change stateNe
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    simp at outputRowNe
  have incrementNonzero :
      (run current index).nextContact.physicalState output -
          (run current index).contact.physicalState output ≠ 0 :=
    sub_ne_zero.mpr outputRowNe
  have causalSplit :
      (run current index).nextContact.physicalState output -
            (run current index).contact.physicalState output =
        wholeRestartCausalTangentGain current index output •
            wholeRestartCrossingUnforcedTangentRow
              current index output +
          ∑' first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
              current index output first :=
    nextContact_sub_contact_eq_causalTangent_add_pairInnovation
      current index output outputNonzero
  exact
    ⟨index, requestedLe, output, outputNonzero,
      incrementNonzero, causalSplit⟩

private theorem nativeIncrement_generates_tangent_or_pairNativeResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (incrementNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0) :
    wholeRestartCrossingUnforcedTangentRow
          initial index output ≠ 0 ∨
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
              initial index output first ≠ 0 ∧
          (wholeRestartNextPairOccurrence
                initial index output first ≠ 0 ∨
            ∃ time :
                Icc (0 : ℝ) (run initial index).nextContact.time.1,
              wholeRestartPairOccurrenceTrace
                initial index output first time ≠ 0) := by
  have causalSplit :
      (run initial index).nextContact.physicalState output -
            (run initial index).contact.physicalState output =
        wholeRestartCausalTangentGain initial index output •
            wholeRestartCrossingUnforcedTangentRow
              initial index output +
          ∑' first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
              initial index output first :=
    nextContact_sub_contact_eq_causalTangent_add_pairInnovation
      initial index output outputNonzero
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow
        initial index output ≠ 0
  · exact Or.inl tangentNonzero
  · right
    have tangentZero :
        wholeRestartCrossingUnforcedTangentRow
          initial index output = 0 :=
      not_ne_iff.mp tangentNonzero
    have aggregateNonzero :
        (∑' first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
            initial index output first) ≠ 0 := by
      intro aggregateZero
      exact incrementNonzero <|
        causalSplit.trans (by
          rw [tangentZero, smul_zero, aggregateZero, add_zero])
    obtain ⟨first, innovationNonzero⟩ :=
      exists_pairInnovation_ne_zero_of_tsum_ne_zero
        initial index output aggregateNonzero
    have pairResponsibility :
        wholeRestartNextPairOccurrence
              initial index output first ≠ 0 ∨
          ∃ time :
              Icc (0 : ℝ) (run initial index).nextContact.time.1,
            wholeRestartPairOccurrenceTrace
              initial index output first time ≠ 0 :=
      wholeRestartPairDuhamelInnovationOccurrence_ne_zero_next_or_trace
        initial index output first innovationNonzero
    exact ⟨first, innovationNonzero, pairResponsibility⟩

/-- A nonzero coefficient increment on an already-generated native edge
selects its own nonzero output and exact same-edge causal disposition. -/
theorem nativeOutputIncrement_ne_zero_generates_causalResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (incrementNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0) :
    output ≠ 0 ∧
      (run initial index).nextContact.physicalState output -
            (run initial index).contact.physicalState output =
          wholeRestartCausalTangentGain initial index output •
              wholeRestartCrossingUnforcedTangentRow
                initial index output +
            (∑' first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                initial index output first) ∧
      (wholeRestartCrossingUnforcedTangentRow
            initial index output ≠ 0 ∨
        ∃ first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
                initial index output first ≠ 0 ∧
            (wholeRestartNextPairOccurrence
                  initial index output first ≠ 0 ∨
              ∃ time :
                  Icc (0 : ℝ)
                    (run initial index).nextContact.time.1,
                wholeRestartPairOccurrenceTrace
                  initial index output first time ≠ 0)) := by
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    simp at incrementNonzero
  have causalSplit :
      (run initial index).nextContact.physicalState output -
            (run initial index).contact.physicalState output =
        wholeRestartCausalTangentGain initial index output •
            wholeRestartCrossingUnforcedTangentRow
              initial index output +
          ∑' first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
              initial index output first :=
    nextContact_sub_contact_eq_causalTangent_add_pairInnovation
      initial index output outputNonzero
  exact
    ⟨outputNonzero, causalSplit,
      nativeIncrement_generates_tangent_or_pairNativeResponsibility
        initial index output outputNonzero incrementNonzero⟩

/-- Every already-generated changed native physical edge has its exact
same-edge causal responsibility.  The changed state selects a nonzero
Fourier output internally; no endpoint atom or crossing certificate is
needed at this consumer layer. -/
theorem nativePhysicalChange_generates_causalResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (stateNe :
      (run initial index).nextContact.physicalState ≠
        (run initial index).contact.physicalState) :
    ∃ output : IntegerWavevector,
      output ≠ 0 ∧
        (run initial index).nextContact.physicalState output -
            (run initial index).contact.physicalState output ≠ 0 ∧
        (run initial index).nextContact.physicalState output -
              (run initial index).contact.physicalState output =
            wholeRestartCausalTangentGain initial index output •
                wholeRestartCrossingUnforcedTangentRow
                  initial index output +
              (∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  initial index output first) ∧
        (wholeRestartCrossingUnforcedTangentRow
              initial index output ≠ 0 ∨
          ∃ first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
                  initial index output first ≠ 0 ∧
              (wholeRestartNextPairOccurrence
                    initial index output first ≠ 0 ∨
                ∃ time :
                    Icc (0 : ℝ)
                      (run initial index).nextContact.time.1,
                  wholeRestartPairOccurrenceTrace
                    initial index output first time ≠ 0)) := by
  obtain ⟨output, outputRowNe⟩ :=
    exists_output_change_of_state_change stateNe
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    simp at outputRowNe
  have incrementNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0 :=
    sub_ne_zero.mpr outputRowNe
  obtain ⟨_outputNonzero, causalSplit, responsibility⟩ :=
    nativeOutputIncrement_ne_zero_generates_causalResponsibility
      initial index output incrementNonzero
  exact
    ⟨output, outputNonzero, incrementNonzero, causalSplit,
      responsibility⟩

/-- A positive atom therefore cofinally produces an actual changed native
edge and its source-owned tangent/pair causal disposition. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_late_nativeCausalResponsibility
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ index : ℕ,
      requestedStart ≤ index ∧
        ∃ output : IntegerWavevector,
          output ≠ 0 ∧
          (run current index).nextContact.physicalState output -
              (run current index).contact.physicalState output ≠ 0 ∧
          (run current index).nextContact.physicalState output -
                (run current index).contact.physicalState output =
              wholeRestartCausalTangentGain current index output •
                  wholeRestartCrossingUnforcedTangentRow
                    current index output +
                (∑' first : IntegerWavevector,
                  wholeRestartPairDuhamelInnovationOccurrence
                    current index output first) ∧
          (wholeRestartCrossingUnforcedTangentRow
                current index output ≠ 0 ∨
            ∃ first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                    current index output first ≠ 0 ∧
                (wholeRestartNextPairOccurrence
                      current index output first ≠ 0 ∨
                  ∃ time :
                      Icc (0 : ℝ)
                        (run current index).nextContact.time.1,
                    wholeRestartPairOccurrenceTrace
                      current index output first time ≠ 0)) := by
  obtain
      ⟨index, requestedLe, output, outputNonzero,
        incrementNonzero, causalSplit⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_late_nativeCausalSplit
      step atomPositive requestedStart
  exact
    ⟨index, requestedLe, output, outputNonzero,
      incrementNonzero, causalSplit,
      nativeIncrement_generates_tangent_or_pairNativeResponsibility
        current index output outputNonzero incrementNonzero⟩

/-! ## Source-owned zero or cofinal active disposition -/

/-- Every actual endpoint macro stage now exhausts its kinetic atom without
a caller-selected branch: either the atom vanishes and the strong interface
closes, or after every requested native index the same old run generates a
changed unforced edge carrying the causal tangent/pair responsibility above. -/
theorem physicalStageKineticEnergyAtom_zero_or_cofinal_nativeCausalResponsibility
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    step.physicalStageKineticEnergyAtom = 0 ∨
      ∀ requestedStart : ℕ,
        ∃ index : ℕ,
          requestedStart ≤ index ∧
            ∃ output : IntegerWavevector,
              output ≠ 0 ∧
              (run current index).nextContact.physicalState output -
                    (run current index).contact.physicalState output ≠ 0 ∧
              (wholeRestartCrossingUnforcedTangentRow
                    current index output ≠ 0 ∨
                ∃ first : IntegerWavevector,
                  wholeRestartPairDuhamelInnovationOccurrence
                        current index output first ≠ 0 ∧
                    (wholeRestartNextPairOccurrence
                          current index output first ≠ 0 ∨
                      ∃ time :
                          Icc (0 : ℝ)
                            (run current index).nextContact.time.1,
                        wholeRestartPairOccurrenceTrace
                          current index output first time ≠ 0)) := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  rcases endpointReceipt.kineticReceipt.defect_disposition with
    defectPositive | defectZero
  · right
    intro requestedStart
    have atomPositive :
        0 < step.physicalStageKineticEnergyAtom := by
      rw [step.physicalStageKineticEnergyAtom_eq_defect]
      exact defectPositive
    obtain
        ⟨index, requestedLe, output, outputNonzero,
          incrementNonzero, _causalSplit, disposition⟩ :=
      physicalStageKineticEnergyAtom_pos_generates_late_nativeCausalResponsibility
        step atomPositive requestedStart
    exact
      ⟨index, requestedLe, output, outputNonzero,
        incrementNonzero, disposition⟩
  · left
    rw [step.physicalStageKineticEnergyAtom_eq_defect]
    exact defectZero.1

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomNativeCausalRedirect
end NavierStokes
end SaturationMonoid
