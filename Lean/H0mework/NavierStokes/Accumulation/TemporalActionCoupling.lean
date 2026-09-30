import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import H0mework.Realization.Fields.RealTemporalAction
import H0mework.NavierStokes.Accumulation.BoundaryDisposition
import H0mework.NavierStokes.KineticRestart.ExactKineticDissipation

/-!
# Native whole-restart temporal action coupling

Every finite occurrence of the original NS boundary source generates the
complete physical coupling between its vorticity scale, local barrier,
guaranteed horizon, late-half successor clock, kinetic potential drop and
mean-density-weighted dissipation.  The coupling stays on the original
actual run and does not classify a boundary branch or assume a future clock.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling

open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition

noncomputable section

/-- Mean whole-vorticity density on the exact successor prefix paid by one
native kinetic edge. -/
def successorMeanWholeVorticityDensity
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) : Real :=
  wholePrefixVorticityMass
      (run initial stage).nextContact.time
      (run initial stage).nextReceipt.stateLimit /
    (run initial stage).nextContact.time.1

/-- Recognition that one original-root occurrence is a finite physical edge.
The constructor retains the source-generated occurrence witness. -/
inductive NativeFiniteTemporalAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    {current : NativeTemporalCurrent initial} ->
      (boundarySource initial).toRootSource.actual.OccurrenceAt current -> Type
  | finite
      (stage : Nat)
      (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
      NativeFiniteTemporalAt initial ⟨.finite, .finite stage occurrence⟩

theorem successorMeanWholeVorticityDensity_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    0 <= successorMeanWholeVorticityDensity initial stage := by
  exact div_nonneg
    (wholePrefixVorticityMass_nonneg _ _)
    (run initial stage).nextContact.time_pos.le

/-- Exact Radon--Nikodym-shaped conversion on one native edge.  The material
action is the successor clock multiplied by its generated kinetic density. -/
theorem kineticDefect_eq_clock_mul_nativeDensity
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    wholeRestartKineticDefect initial stage =
      (run initial (stage + 1)).contact.time.1 *
        (2 * nu.coeff * successorMeanWholeVorticityDensity initial stage) := by
  have timeNe : (run initial stage).nextContact.time.1 ≠ 0 :=
    ne_of_gt (run initial stage).nextContact.time_pos
  change
    2 * nu.coeff *
        wholePrefixVorticityMass
          (run initial stage).nextContact.time
          (run initial stage).nextReceipt.stateLimit =
      (run initial (stage + 1)).contact.time.1 *
        (2 * nu.coeff *
          (wholePrefixVorticityMass
              (run initial stage).nextContact.time
              (run initial stage).nextReceipt.stateLimit /
            (run initial stage).nextContact.time.1))
  rw [run_succ]
  change
    2 * nu.coeff *
        wholePrefixVorticityMass
          (run initial stage).nextContact.time
          (run initial stage).nextReceipt.stateLimit =
      (run initial stage).nextContact.time.1 *
        (2 * nu.coeff *
          (wholePrefixVorticityMass
              (run initial stage).nextContact.time
              (run initial stage).nextReceipt.stateLimit /
            (run initial stage).nextContact.time.1))
  field_simp

private noncomputable def nativeFiniteTemporalCoupling
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    {occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current}
    (temporal : NativeFiniteTemporalAt initial occurrence) :
    SourceNativeTemporalActionCouplingAt
      (realTemporalActionCalculus
        (sourceOwnedWholeStateBarrierSlope nu)) := by
  cases temporal with
  | finite stage finiteOccurrence =>
      let entropyDefect :=
        sourceGeneratedWholeRestartKineticEntropyDefect initial stage
      refine
        { scale := restartCoefficientCeiling initial stage
          barrier := restartBarrierSlope initial stage
          horizon := wholeRestartDuration (run initial stage).contact
          clock := (run initial (stage + 1)).contact.time.1
          sourcePotential := wholeRestartKineticEntropy initial stage
          targetPotential := wholeRestartKineticEntropy initial (stage + 1)
          action := wholeRestartKineticDefect initial stage
          density := 2 * nu.coeff *
            successorMeanWholeVorticityDensity initial stage
          scale_admissible := (restartCoefficientCeiling_pos initial stage).le
          barrier_positive := restartBarrierSlope_pos initial stage
          horizon_positive := wholeRestartDuration_pos (run initial stage).contact
          clock_positive := run_contact_time_pos initial (stage + 1)
          barrier_eq_scale := rfl
          horizon_eq := rfl
          late_clock := by
            simpa only [run_succ, next_duration] using
              run_contact_time_half_duration_lt initial (stage + 1)
          clock_within := by
            have clockLe := (run initial (stage + 1)).contact.time.2.2
            simpa only [run_succ, next_duration] using clockLe
          sourcePotential_nonnegative := by
            exact puncturedWholeVorticityKineticMass_nonneg _
          targetPotential_nonnegative := by
            exact puncturedWholeVorticityKineticMass_nonneg _
          action_nonnegative := entropyDefect.defect_nonneg
          density_nonnegative := mul_nonneg
            (mul_nonneg (by norm_num) nu.coeff_pos.le)
            (successorMeanWholeVorticityDensity_nonneg initial stage)
          action_eq_potential_drop := by
            linarith [entropyDefect.balance]
          action_eq_clock_density :=
            kineticDefect_eq_clock_mul_nativeDensity initial stage }

/-- Original-root temporal coupling law.  Its only temporal witnesses are
actual finite occurrences of the same boundary source. -/
noncomputable def sourceGeneratedNativeTemporalActionCouplingLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeTemporalActionCouplingLaw
      (boundaryLedgerSource initial)
      (realTemporalActionCalculus
        (sourceOwnedWholeStateBarrierSlope nu)) where
  TemporalAt := NativeFiniteTemporalAt initial
  couplingAt := fun _occurrence temporal =>
    nativeFiniteTemporalCoupling initial temporal

/-- Canonical coupling generated at stage `stage` of the fixed actual run. -/
noncomputable def sourceGeneratedNativeTemporalActionCouplingAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    SourceNativeTemporalActionCouplingAt
      (realTemporalActionCalculus
        (sourceOwnedWholeStateBarrierSlope nu)) :=
  (sourceGeneratedNativeTemporalActionCouplingLaw initial).couplingAt
    ⟨.finite, .finite stage
      (generatedWholeRestartNativeActualOccurrence initial stage)⟩
    (.finite stage
      (generatedWholeRestartNativeActualOccurrence initial stage))

@[simp] theorem sourceGeneratedNativeTemporalActionCouplingAt_clock
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (sourceGeneratedNativeTemporalActionCouplingAt initial stage).clock =
      (run initial (stage + 1)).contact.time.1 := by
  simp only [sourceGeneratedNativeTemporalActionCouplingAt,
    sourceGeneratedNativeTemporalActionCouplingLaw,
    nativeFiniteTemporalCoupling]

@[simp] theorem sourceGeneratedNativeTemporalActionCouplingAt_action
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (sourceGeneratedNativeTemporalActionCouplingAt initial stage).action =
      wholeRestartKineticDefect initial stage := by
  simp only [sourceGeneratedNativeTemporalActionCouplingAt,
    sourceGeneratedNativeTemporalActionCouplingLaw,
    nativeFiniteTemporalCoupling]

@[simp] theorem sourceGeneratedNativeTemporalActionCouplingAt_density
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (sourceGeneratedNativeTemporalActionCouplingAt initial stage).density =
      2 * nu.coeff * successorMeanWholeVorticityDensity initial stage := by
  simp only [sourceGeneratedNativeTemporalActionCouplingAt,
    sourceGeneratedNativeTemporalActionCouplingLaw,
    nativeFiniteTemporalCoupling]

@[simp] theorem sourceGeneratedNativeTemporalActionCouplingAt_scale
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (sourceGeneratedNativeTemporalActionCouplingAt initial stage).scale =
      restartCoefficientCeiling initial stage := by
  simp only [sourceGeneratedNativeTemporalActionCouplingAt,
    sourceGeneratedNativeTemporalActionCouplingLaw,
    nativeFiniteTemporalCoupling]

@[simp] theorem sourceGeneratedNativeTemporalActionCouplingAt_barrier
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (sourceGeneratedNativeTemporalActionCouplingAt initial stage).barrier =
      restartBarrierSlope initial stage := by
  simp only [sourceGeneratedNativeTemporalActionCouplingAt,
    sourceGeneratedNativeTemporalActionCouplingLaw,
    nativeFiniteTemporalCoupling]

@[simp] theorem sourceGeneratedNativeTemporalActionCouplingAt_horizon
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (sourceGeneratedNativeTemporalActionCouplingAt initial stage).horizon =
      1 / (2 * restartBarrierSlope initial stage) := by
  simp only [sourceGeneratedNativeTemporalActionCouplingAt,
    sourceGeneratedNativeTemporalActionCouplingLaw,
    nativeFiniteTemporalCoupling, wholeRestartDuration,
    sourceOwnedWholeStateDuration, restartBarrierSlope,
    restartCoefficientCeiling]

/-- Every actual edge exposes its silent/faithful density stratum.  This is
a real-valued readout of the generated coupling, not a root disposition. -/
theorem sourceGeneratedNativeTemporalActionCouplingAt_densityStratum
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (sourceGeneratedNativeTemporalActionCouplingAt initial stage).density = 0 ∨
      0 < (sourceGeneratedNativeTemporalActionCouplingAt initial stage).density :=
  (sourceGeneratedNativeTemporalActionCouplingAt initial stage
    ).real_densityStratum

private theorem temporalActionCoupling_eq_iff_data_eq
    {calculus : SourceNativeTemporalActionCalculus}
    (left right : SourceNativeTemporalActionCouplingAt calculus) :
    left = right ↔
      left.scale = right.scale ∧
      left.barrier = right.barrier ∧
      left.horizon = right.horizon ∧
      left.clock = right.clock ∧
      left.sourcePotential = right.sourcePotential ∧
      left.targetPotential = right.targetPotential ∧
      left.action = right.action ∧
      left.density = right.density := by
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rcases left with ⟨leftScale, leftBarrier, leftHorizon, leftClock,
      leftSourcePotential, leftTargetPotential, leftAction, leftDensity,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    rcases right with ⟨rightScale, rightBarrier, rightHorizon, rightClock,
      rightSourcePotential, rightTargetPotential, rightAction, rightDensity,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    simp only at *
    rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-- Equal quantized scale fixes the complete scale/barrier/horizon geometry,
but it does not erase material differences.  Full coupling equality is
exactly the remaining equality of clock, both potentials, action and density.
This is a diagnostic reduction, not a source faithfulness producer. -/
theorem sourceGeneratedNativeTemporalActionCoupling_eq_iff_of_scale_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (left right : Nat)
    (sameScale : restartCoefficientCeiling initial left =
      restartCoefficientCeiling initial right) :
    sourceGeneratedNativeTemporalActionCouplingAt initial left =
        sourceGeneratedNativeTemporalActionCouplingAt initial right ↔
      (sourceGeneratedNativeTemporalActionCouplingAt initial left).clock =
          (sourceGeneratedNativeTemporalActionCouplingAt initial right).clock ∧
        (sourceGeneratedNativeTemporalActionCouplingAt
            initial left).sourcePotential =
          (sourceGeneratedNativeTemporalActionCouplingAt
            initial right).sourcePotential ∧
        (sourceGeneratedNativeTemporalActionCouplingAt
            initial left).targetPotential =
          (sourceGeneratedNativeTemporalActionCouplingAt
            initial right).targetPotential ∧
        (sourceGeneratedNativeTemporalActionCouplingAt initial left).action =
          (sourceGeneratedNativeTemporalActionCouplingAt initial right).action ∧
        (sourceGeneratedNativeTemporalActionCouplingAt initial left).density =
          (sourceGeneratedNativeTemporalActionCouplingAt initial right).density := by
  let leftEdge := sourceGeneratedNativeTemporalActionCouplingAt initial left
  let rightEdge := sourceGeneratedNativeTemporalActionCouplingAt initial right
  have scaleEq : leftEdge.scale = rightEdge.scale := by
    simpa only [leftEdge, rightEdge,
      sourceGeneratedNativeTemporalActionCouplingAt_scale] using sameScale
  have barrierEq : leftEdge.barrier = rightEdge.barrier := by
    calc
      leftEdge.barrier =
          (realTemporalActionCalculus
            (sourceOwnedWholeStateBarrierSlope nu)).barrierFromScale
              leftEdge.scale := leftEdge.barrier_eq_scale
      _ = (realTemporalActionCalculus
            (sourceOwnedWholeStateBarrierSlope nu)).barrierFromScale
              rightEdge.scale := congrArg _ scaleEq
      _ = rightEdge.barrier := rightEdge.barrier_eq_scale.symm
  have horizonEq : leftEdge.horizon = rightEdge.horizon := by
    calc
      leftEdge.horizon =
          (realTemporalActionCalculus
            (sourceOwnedWholeStateBarrierSlope nu)).horizonFromBarrier
              leftEdge.barrier := leftEdge.horizon_eq
      _ = (realTemporalActionCalculus
            (sourceOwnedWholeStateBarrierSlope nu)).horizonFromBarrier
              rightEdge.barrier := congrArg _ barrierEq
      _ = rightEdge.horizon := rightEdge.horizon_eq.symm
  rw [temporalActionCoupling_eq_iff_data_eq]
  simp only [scaleEq, barrierEq, horizonEq, true_and, leftEdge, rightEdge]

/-- The current operational carrier remembers the actual stage.  Equality of
two complete finite operational records is therefore exactly equality of
their occurrence indices, regardless of any equality between coarse physical
readouts. -/
theorem boundaryFiniteOperational_eq_iff_stage_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (left right : Nat) :
    boundaryPositiveRowOperationalAtLower initial
          (boundaryEmitted initial (.finite left)) =
        boundaryPositiveRowOperationalAtLower initial
          (boundaryEmitted initial (.finite right)) ↔
      left = right := by
  constructor
  · intro operationalEq
    exact congrArg BoundaryFiniteEffectOperational.stage operationalEq
  · intro stageEq
    subst right
    rfl

/-- Making the quantized ceiling a faithful coordinate for the complete
finite operational standing is not an adapter theorem: it is logically
equivalent to the missing injectivity of the actual ceiling lineage. -/
theorem restartCoefficientCeiling_completeOperationalFaithful_iff_injective
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (∀ left right,
        restartCoefficientCeiling initial left =
            restartCoefficientCeiling initial right →
          boundaryPositiveRowOperationalAtLower initial
              (boundaryEmitted initial (.finite left)) =
            boundaryPositiveRowOperationalAtLower initial
              (boundaryEmitted initial (.finite right))) ↔
      Function.Injective (restartCoefficientCeiling initial) := by
  constructor
  · intro faithful left right sameCeiling
    exact (boundaryFiniteOperational_eq_iff_stage_eq initial left right).1
      (faithful left right sameCeiling)
  · intro injective left right sameCeiling
    exact (boundaryFiniteOperational_eq_iff_stage_eq initial left right).2
      (injective sameCeiling)

/-! ## Conditional faithful-scale barrier fold -/

private def sourceOwnedBarrierReferenceWave : IntegerWavevector := ![1, 0, 0]

private theorem sourceOwnedBarrierReferenceWave_ne_zero :
    sourceOwnedBarrierReferenceWave ≠ 0 := by
  intro equality
  have coordinateEq := congrFun equality 0
  norm_num [sourceOwnedBarrierReferenceWave] at coordinateEq

/-- If a source-specific faithfulness theorem makes the actual quantized
ceiling injective, the already generated fixed-wave core floor turns the
reciprocal barrier into a p-series.  Injectivity remains an explicit
conditional input here; causal-visit freshness does not manufacture it. -/
theorem summable_reciprocalBarrier_of_restartCoefficientCeiling_injective
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (injective : Function.Injective (restartCoefficientCeiling initial)) :
    Summable fun index => (restartBarrierSlope initial index)⁻¹ := by
  let coefficientFloor := sourceOwnedLocalFixedWaveQuadraticFloor
    nu sourceOwnedBarrierReferenceWave
  have coefficientFloorPos : 0 < coefficientFloor := by
    exact sourceOwnedLocalFixedWaveQuadraticFloor_pos
      nu sourceOwnedBarrierReferenceWave sourceOwnedBarrierReferenceWave_ne_zero
  rcases eventually_sourceOwnedLocalFixedWaveBarrierFloor_le
      nu sourceOwnedBarrierReferenceWave sourceOwnedBarrierReferenceWave_ne_zero with
    ⟨scaleFloor, barrierFloor⟩
  let offset := Nat.ceil (max scaleFloor 0)
  have offsetCastGe : scaleFloor ≤ (offset : Real) := by
    exact (le_max_left scaleFloor 0).trans
      (Nat.le_ceil (max scaleFloor 0))
  have scaleFormula :=
    restartCoefficientCeiling_eq_initial_add_index_of_injective
      initial injective
  have initialScaleOne : 1 ≤ restartCoefficientCeiling initial 0 := by
    have initialScalePos := restartCoefficientCeiling_pos initial 0
    change 1 ≤ (wholeRestartCoefficientLevel initial.contact : Real)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro levelZero
      have ceilingZero : restartCoefficientCeiling initial 0 = 0 := by
        change (wholeRestartCoefficientLevel initial.contact : Real) = 0
        exact_mod_cast levelZero
      linarith))
  have shiftedMajorant : ∀ index : Nat,
      (restartBarrierSlope initial (offset + index))⁻¹ ≤
        coefficientFloor⁻¹ *
          (1 / (((index + 1 : Nat) : Real) ^ 2)) := by
    intro index
    have scaleGeFloor : scaleFloor ≤
        restartCoefficientCeiling initial (offset + index) := by
      rw [scaleFormula (offset + index)]
      have offsetLe : (offset : Real) ≤
          restartCoefficientCeiling initial 0 + (offset + index : Nat) := by
        norm_num [Nat.cast_add]
        linarith [initialScaleOne]
      exact offsetCastGe.trans offsetLe
    have barrierLe := barrierFloor
      (restartCoefficientCeiling initial (offset + index)) scaleGeFloor
    change
      coefficientFloor *
            restartCoefficientCeiling initial (offset + index) ^ 2 + 1 ≤
        restartBarrierSlope initial (offset + index) at barrierLe
    have indexScaleLe : ((index + 1 : Nat) : Real) ≤
        restartCoefficientCeiling initial (offset + index) := by
      rw [scaleFormula (offset + index)]
      norm_num [Nat.cast_add]
      linarith [initialScaleOne]
    have squareLe : (((index + 1 : Nat) : Real) ^ 2) ≤
        restartCoefficientCeiling initial (offset + index) ^ 2 := by
      nlinarith [sq_nonneg
        (restartCoefficientCeiling initial (offset + index) -
          ((index + 1 : Nat) : Real))]
    have modelLeBarrier :
        coefficientFloor * (((index + 1 : Nat) : Real) ^ 2) ≤
          restartBarrierSlope initial (offset + index) := by
      have scaledLe := mul_le_mul_of_nonneg_left squareLe
        coefficientFloorPos.le
      exact scaledLe.trans (by linarith [barrierLe])
    have modelPos :
        0 < coefficientFloor * (((index + 1 : Nat) : Real) ^ 2) := by
      exact mul_pos coefficientFloorPos (sq_pos_of_pos (by positivity))
    have reciprocalLe :
        (restartBarrierSlope initial (offset + index))⁻¹ ≤
          (coefficientFloor * (((index + 1 : Nat) : Real) ^ 2))⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le modelPos modelLeBarrier)
    calc
      (restartBarrierSlope initial (offset + index))⁻¹ ≤
          (coefficientFloor * (((index + 1 : Nat) : Real) ^ 2))⁻¹ :=
        reciprocalLe
      _ = coefficientFloor⁻¹ *
          (1 / (((index + 1 : Nat) : Real) ^ 2)) := by
        rw [mul_inv_rev]
        simp only [one_div, mul_comm]
  have pSeries : Summable fun index : Nat =>
      1 / (((index + 1 : Nat) : Real) ^ 2) := by
    have base : Summable fun index : Nat =>
        1 / ((index : Real) ^ (2 : Nat)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (base.comp_injective Nat.succ_injective).congr fun index => by
      simp only [Function.comp_apply, Nat.cast_succ]
  have shiftedSummable : Summable fun index =>
      (restartBarrierSlope initial (offset + index))⁻¹ := by
    exact (pSeries.mul_left coefficientFloor⁻¹).of_nonneg_of_le
      (fun index => inv_nonneg.mpr
        (restartBarrierSlope_pos initial (offset + index)).le)
      shiftedMajorant
  rw [← summable_nat_add_iff (f := fun index =>
    (restartBarrierSlope initial index)⁻¹) offset]
  simpa only [Nat.add_comm] using shiftedSummable

private theorem thirteenHalf_potential_step
    {base debit charge : Real}
    (basePos : 0 < base)
    (debitNonneg : 0 ≤ debit)
    (charged : charge ≤ base ^ (11 / 2 : Real) * debit) :
    base ^ (13 / 2 : Real) + charge ≤
      (base + debit) ^ (13 / 2 : Real) := by
  let ratio : Real := debit / base
  have ratioNonneg : 0 ≤ ratio :=
    div_nonneg debitNonneg basePos.le
  have bernoulli := one_add_mul_self_le_rpow_one_add
    (p := (13 / 2 : Real)) (s := ratio) (by linarith) (by norm_num)
  have basePowerNonneg : 0 ≤ base ^ (13 / 2 : Real) :=
    Real.rpow_nonneg basePos.le _
  have scaledBernoulli :=
    mul_le_mul_of_nonneg_left bernoulli basePowerNonneg
  have powerDiv :
      base ^ (13 / 2 : Real) / base =
        base ^ (11 / 2 : Real) := by
    rw [← Real.rpow_sub_one basePos.ne' (13 / 2 : Real)]
    congr 1
    norm_num
  have leftEq :
      base ^ (13 / 2 : Real) *
          (1 + (13 / 2 : Real) * ratio) =
        base ^ (13 / 2 : Real) +
          (13 / 2 : Real) * base ^ (11 / 2 : Real) * debit := by
    dsimp only [ratio]
    rw [show base ^ (13 / 2 : Real) *
          (1 + (13 / 2 : Real) * (debit / base)) =
        base ^ (13 / 2 : Real) +
          (13 / 2 : Real) *
            (base ^ (13 / 2 : Real) / base) * debit by ring,
      powerDiv]
  have onePlusRatioNonneg : 0 ≤ 1 + ratio := by linarith
  have rightEq :
      base ^ (13 / 2 : Real) *
          (1 + ratio) ^ (13 / 2 : Real) =
        (base + debit) ^ (13 / 2 : Real) := by
    rw [← Real.mul_rpow basePos.le onePlusRatioNonneg]
    congr 1
    dsimp only [ratio]
    field_simp [basePos.ne']
  have potentialStep :
      base ^ (13 / 2 : Real) +
          (13 / 2 : Real) * base ^ (11 / 2 : Real) * debit ≤
        (base + debit) ^ (13 / 2 : Real) := by
    rw [← leftEq, ← rightEq]
    exact scaledBernoulli
  have weightedDebitNonneg :
      0 ≤ base ^ (11 / 2 : Real) * debit :=
    mul_nonneg (Real.rpow_nonneg basePos.le _) debitNonneg
  linarith

/-- A scale-relative physical mass debit generates the exact `2/13` scale
growth consumed by the seventh-order barrier.  The input is one same-edge
physical law; recurrence and summability are conclusions of the fold. -/
theorem scaled_thirteenHalf_scale_growth_of_massDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (charge : Real)
    (chargePos : 0 < charge)
    (debit : ∀ index : Nat,
      charge /
          (restartPhysicalVorticityMass initial index + 1) ^
            (11 / 2 : Real) ≤
        restartPhysicalVorticityMass initial (index + 1) -
          restartPhysicalVorticityMass initial index) :
    ∃ amplitude : Real, 0 < amplitude ∧
      ∀ index : Nat,
        amplitude * (((index + 1 : Nat) : Real) ^ (2 / 13 : Real)) ≤
          restartCoefficientCeiling initial index := by
  let massBase : Nat → Real := fun index =>
    restartPhysicalVorticityMass initial index + 1
  have massBasePos : ∀ index, 0 < massBase index := by
    intro index
    have massNonneg :
        0 ≤ restartPhysicalVorticityMass initial index := by
      unfold restartPhysicalVorticityMass
      exact wholeVorticityEuclideanMass_nonneg _
    dsimp only [massBase]
    linarith
  have potentialGrowth : ∀ index : Nat,
      massBase 0 ^ (13 / 2 : Real) + (index : Real) * charge ≤
        massBase index ^ (13 / 2 : Real) := by
    intro index
    induction index with
    | zero => simp
    | succ index inductionHypothesis =>
        let edgeDebit :=
          restartPhysicalVorticityMass initial (index + 1) -
            restartPhysicalVorticityMass initial index
        have denominatorPos :
            0 < massBase index ^ (11 / 2 : Real) :=
          Real.rpow_pos_of_pos (massBasePos index) _
        have debitLower :
            charge / massBase index ^ (11 / 2 : Real) ≤ edgeDebit := by
          simpa only [massBase, edgeDebit] using debit index
        have edgeDebitPos : 0 < edgeDebit :=
          (div_pos chargePos denominatorPos).trans_le debitLower
        have charged :
            charge ≤ massBase index ^ (11 / 2 : Real) * edgeDebit := by
          have := (div_le_iff₀ denominatorPos).1 debitLower
          nlinarith
        have step := thirteenHalf_potential_step
          (massBasePos index) edgeDebitPos.le charged
        have nextBase : massBase (index + 1) = massBase index + edgeDebit := by
          dsimp only [massBase, edgeDebit]
          ring
        rw [nextBase]
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith
  let initialPotential := massBase 0 ^ (13 / 2 : Real)
  let commonCharge := min charge initialPotential
  have initialPotentialPos : 0 < initialPotential :=
    Real.rpow_pos_of_pos (massBasePos 0) _
  have commonChargePos : 0 < commonCharge :=
    lt_min chargePos initialPotentialPos
  let amplitude := commonCharge ^ (2 / 13 : Real)
  have amplitudePos : 0 < amplitude :=
    Real.rpow_pos_of_pos commonChargePos _
  refine ⟨amplitude, amplitudePos, ?_⟩
  intro index
  have commonLeCharge : commonCharge ≤ charge := min_le_left _ _
  have commonLeInitial : commonCharge ≤ initialPotential := min_le_right _ _
  have sourcePowerLower :
      (((index + 1 : Nat) : Real) * commonCharge) ≤
        massBase index ^ (13 / 2 : Real) := by
    have growth := potentialGrowth index
    have indexNonneg : 0 ≤ (index : Real) := Nat.cast_nonneg index
    have indexScaled : (index : Real) * commonCharge ≤
        (index : Real) * charge :=
      mul_le_mul_of_nonneg_left commonLeCharge indexNonneg
    norm_num [Nat.cast_add, Nat.cast_one]
    dsimp only [initialPotential] at commonLeInitial
    linarith
  have sourcePowerNonneg :
      0 ≤ ((index + 1 : Nat) : Real) * commonCharge := by positivity
  have rootLower := Real.rpow_le_rpow sourcePowerNonneg sourcePowerLower
    (by norm_num : (0 : Real) ≤ 2 / 13)
  have cancelPower :
      (massBase index ^ (13 / 2 : Real)) ^ (2 / 13 : Real) =
        massBase index := by
    rw [← Real.rpow_mul (massBasePos index).le]
    norm_num
  have baseScaleLower :
      amplitude * (((index + 1 : Nat) : Real) ^ (2 / 13 : Real)) ≤
        massBase index := by
    rw [show amplitude * (((index + 1 : Nat) : Real) ^ (2 / 13 : Real)) =
        (((index + 1 : Nat) : Real) * commonCharge) ^
          (2 / 13 : Real) by
      dsimp only [amplitude]
      rw [Real.mul_rpow (by positivity) commonChargePos.le]
      ring]
    exact rootLower.trans_eq cancelPower
  have massBaseLeCeiling :
      massBase index ≤ restartCoefficientCeiling initial index := by
    unfold massBase restartPhysicalVorticityMass restartCoefficientCeiling
    change
      wholeVorticityEuclideanMass
            (run initial index).contact.physicalState + 1 ≤
        (wholeRestartCoefficientLevel (run initial index).contact : Real)
    unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    exact Nat.le_ceil _
  exact baseScaleLower.trans massBaseLeCeiling

/-- The scale growth dictated by a `scale⁻¹¹ᐟ²` residence debit is already
enough for the canonical seventh-order barrier.  Any positive source-owned
amplitude is retained: `a * (n + 1)^(2/13)` in scale becomes the summable
p-series exponent `14/13` in the reciprocal clock. -/
theorem summable_reciprocalBarrier_of_scaled_thirteenHalf_scale_growth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (amplitude : Real)
    (amplitudePos : 0 < amplitude)
    (growth : ∀ index : Nat,
      amplitude * (((index + 1 : Nat) : Real) ^ (2 / 13 : Real)) ≤
        restartCoefficientCeiling initial index) :
    Summable fun index => (restartBarrierSlope initial index)⁻¹ := by
  let coefficient :=
    sourceOwnedWholeStateBarrierSeventhCoefficient nu * amplitude ^ 7
  have coefficientPos : 0 < coefficient :=
    mul_pos (sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu)
      (pow_pos amplitudePos 7)
  have majorant : ∀ index : Nat,
      (restartBarrierSlope initial index)⁻¹ ≤
        coefficient⁻¹ *
          (1 / (((index + 1 : Nat) : Real) ^ (14 / 13 : Real))) := by
    intro index
    let base : Real := ((index + 1 : Nat) : Real)
    have basePos : 0 < base := by
      dsimp only [base]
      positivity
    have scalePos :
        0 < restartCoefficientCeiling initial index :=
      restartCoefficientCeiling_pos initial index
    have rootNonneg : 0 ≤ base ^ (2 / 13 : Real) :=
      Real.rpow_nonneg basePos.le _
    have basePowerEq :
        base ^ (14 / 13 : Real) =
          (base ^ (2 / 13 : Real)) ^ (7 : Nat) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul basePos.le]
      congr 1
      norm_num
    have seventhLe :
        amplitude ^ 7 * base ^ (14 / 13 : Real) ≤
          restartCoefficientCeiling initial index ^ 7 := by
      calc
        amplitude ^ 7 * base ^ (14 / 13 : Real) =
            (amplitude * base ^ (2 / 13 : Real)) ^ 7 := by
          rw [basePowerEq, mul_pow]
        _ ≤ restartCoefficientCeiling initial index ^ 7 :=
          pow_le_pow_left₀
            (mul_nonneg amplitudePos.le rootNonneg) (growth index) 7
    have barrierLower := sourceOwnedWholeStateBarrierSeventh_le
      nu (restartCoefficientCeiling initial index) scalePos.le
    change
      sourceOwnedWholeStateBarrierSeventhCoefficient nu *
          restartCoefficientCeiling initial index ^ 7 + 1 ≤
        restartBarrierSlope initial index at barrierLower
    have modelLeBarrier :
        coefficient * base ^ (14 / 13 : Real) ≤
          restartBarrierSlope initial index := by
      have scaled := mul_le_mul_of_nonneg_left seventhLe
        (sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu).le
      dsimp only [coefficient]
      calc
        sourceOwnedWholeStateBarrierSeventhCoefficient nu * amplitude ^ 7 *
              base ^ (14 / 13 : Real) =
            sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              (amplitude ^ 7 * base ^ (14 / 13 : Real)) := by ring
        _ ≤ sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              restartCoefficientCeiling initial index ^ 7 := scaled
        _ ≤ restartBarrierSlope initial index := by linarith [barrierLower]
    have modelPos :
        0 < coefficient * base ^ (14 / 13 : Real) :=
      mul_pos coefficientPos (Real.rpow_pos_of_pos basePos _)
    have reciprocalLe :
        (restartBarrierSlope initial index)⁻¹ ≤
          (coefficient * base ^ (14 / 13 : Real))⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le modelPos modelLeBarrier)
    calc
      (restartBarrierSlope initial index)⁻¹ ≤
          (coefficient * base ^ (14 / 13 : Real))⁻¹ := reciprocalLe
      _ = coefficient⁻¹ *
          (1 / (((index + 1 : Nat) : Real) ^ (14 / 13 : Real))) := by
        rw [mul_inv_rev]
        simp only [one_div, base, mul_comm]
  have pSeries : Summable fun index : Nat =>
      1 / (((index + 1 : Nat) : Real) ^ (14 / 13 : Real)) := by
    have baseSeries : Summable fun index : Nat =>
        1 / ((index : Real) ^ (14 / 13 : Real)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    exact (baseSeries.comp_injective Nat.succ_injective).congr fun index => by
      simp only [Function.comp_apply, Nat.cast_succ]
  exact (pSeries.mul_left coefficient⁻¹).of_nonneg_of_le
    (fun index => inv_nonneg.mpr
      (restartBarrierSlope_pos initial index).le)
    majorant

theorem summable_reciprocalBarrier_of_thirteenHalf_scale_growth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (growth : ∀ index : Nat,
      (((index + 1 : Nat) : Real) ^ (2 / 13 : Real)) ≤
        restartCoefficientCeiling initial index) :
    Summable fun index => (restartBarrierSlope initial index)⁻¹ :=
  summable_reciprocalBarrier_of_scaled_thirteenHalf_scale_growth
    initial 1 (by norm_num) (by simpa using growth)

private theorem summable_halfIndexSquare :
    Summable fun index : Nat =>
      1 / ((((index / 2 + 1 : Nat) : Real)) ^ 2) := by
  have pSeries : Summable fun index : Nat =>
      1 / (((index + 1 : Nat) : Real) ^ 2) := by
    have base : Summable fun index : Nat =>
        1 / ((index : Real) ^ (2 : Nat)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (base.comp_injective Nat.succ_injective).congr fun index => by
      simp only [Function.comp_apply, Nat.cast_succ]
  apply (pSeries.mul_left 4).of_nonneg_of_le
  · intro index
    positivity
  · intro index
    let halfIndex : Real := ((index / 2 + 1 : Nat) : Real)
    let successorIndex : Real := ((index + 1 : Nat) : Real)
    have successorIndexPos : 0 < successorIndex := by
      dsimp only [successorIndex]
      positivity
    have halfIndexPos : 0 < halfIndex := by
      dsimp only [halfIndex]
      positivity
    have successorIndexLe : successorIndex ≤ 2 * halfIndex := by
      dsimp only [successorIndex, halfIndex]
      exact_mod_cast
        (show index + 1 ≤ 2 * (index / 2 + 1) by omega)
    have halfLe : successorIndex / 2 ≤ halfIndex := by linarith
    have halfSquareLe : (successorIndex / 2) ^ 2 ≤ halfIndex ^ 2 := by
      nlinarith [sq_nonneg (halfIndex - successorIndex / 2)]
    have reciprocalLe := one_div_le_one_div_of_le
      (sq_pos_of_pos (div_pos successorIndexPos (by norm_num))) halfSquareLe
    calc
      1 / halfIndex ^ 2 ≤ 1 / (successorIndex / 2) ^ 2 := reciprocalLe
      _ = 4 * (1 / successorIndex ^ 2) := by
        field_simp [successorIndexPos.ne']
        ring

/-- The weaker two-edge growth generated by immediate residual settlement
already suffices for the same p=2 barrier fold. -/
theorem summable_reciprocalBarrier_of_halfIndex_level_growth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (growth : ∀ index : Nat,
      index / 2 ≤ restartCoefficientLevelNat initial index) :
    Summable fun index => (restartBarrierSlope initial index)⁻¹ := by
  let coefficientFloor := sourceOwnedLocalFixedWaveQuadraticFloor
    nu sourceOwnedBarrierReferenceWave
  have coefficientFloorPos : 0 < coefficientFloor := by
    exact sourceOwnedLocalFixedWaveQuadraticFloor_pos
      nu sourceOwnedBarrierReferenceWave sourceOwnedBarrierReferenceWave_ne_zero
  rcases eventually_sourceOwnedLocalFixedWaveBarrierFloor_le
      nu sourceOwnedBarrierReferenceWave sourceOwnedBarrierReferenceWave_ne_zero with
    ⟨scaleFloor, barrierFloor⟩
  let baseOffset := Nat.ceil (max scaleFloor 0)
  let offset := 2 * baseOffset + 2
  have baseOffsetCastGe : scaleFloor ≤ (baseOffset : Real) := by
    exact (le_max_left scaleFloor 0).trans
      (Nat.le_ceil (max scaleFloor 0))
  have shiftedMajorant : ∀ index : Nat,
      (restartBarrierSlope initial (offset + index))⁻¹ ≤
        coefficientFloor⁻¹ *
          (1 / ((((index / 2 + 1 : Nat) : Real)) ^ 2)) := by
    intro index
    have indexScaleLeNat : index / 2 + 1 ≤
        restartCoefficientLevelNat initial (offset + index) := by
      have offsetHalfLe : index / 2 + 1 ≤ (offset + index) / 2 := by
        dsimp only [offset]
        omega
      exact offsetHalfLe.trans (growth (offset + index))
    have baseOffsetLeScaleNat : baseOffset ≤
        restartCoefficientLevelNat initial (offset + index) := by
      have baseLeHalf : baseOffset ≤ (offset + index) / 2 := by
        dsimp only [offset]
        omega
      exact baseLeHalf.trans (growth (offset + index))
    have scaleGeFloor : scaleFloor ≤
        restartCoefficientCeiling initial (offset + index) := by
      rw [restartCoefficientCeiling_eq_levelNat_cast]
      exact baseOffsetCastGe.trans (by exact_mod_cast baseOffsetLeScaleNat)
    have barrierLe := barrierFloor
      (restartCoefficientCeiling initial (offset + index)) scaleGeFloor
    change
      coefficientFloor *
            restartCoefficientCeiling initial (offset + index) ^ 2 + 1 ≤
        restartBarrierSlope initial (offset + index) at barrierLe
    have indexScaleLe : (((index / 2 + 1 : Nat) : Real)) ≤
        restartCoefficientCeiling initial (offset + index) := by
      rw [restartCoefficientCeiling_eq_levelNat_cast]
      exact_mod_cast indexScaleLeNat
    have squareLe : ((((index / 2 + 1 : Nat) : Real)) ^ 2) ≤
        restartCoefficientCeiling initial (offset + index) ^ 2 := by
      nlinarith [sq_nonneg
        (restartCoefficientCeiling initial (offset + index) -
          ((index / 2 + 1 : Nat) : Real))]
    have modelLeBarrier :
        coefficientFloor * ((((index / 2 + 1 : Nat) : Real)) ^ 2) ≤
          restartBarrierSlope initial (offset + index) := by
      have scaledLe := mul_le_mul_of_nonneg_left squareLe
        coefficientFloorPos.le
      exact scaledLe.trans (by linarith [barrierLe])
    have modelPos :
        0 < coefficientFloor * ((((index / 2 + 1 : Nat) : Real)) ^ 2) := by
      exact mul_pos coefficientFloorPos (sq_pos_of_pos (by positivity))
    have reciprocalLe :
        (restartBarrierSlope initial (offset + index))⁻¹ ≤
          (coefficientFloor *
            ((((index / 2 + 1 : Nat) : Real)) ^ 2))⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le modelPos modelLeBarrier)
    calc
      (restartBarrierSlope initial (offset + index))⁻¹ ≤
          (coefficientFloor *
            ((((index / 2 + 1 : Nat) : Real)) ^ 2))⁻¹ := reciprocalLe
      _ = coefficientFloor⁻¹ *
          (1 / ((((index / 2 + 1 : Nat) : Real)) ^ 2)) := by
        rw [mul_inv_rev]
        simp only [one_div, mul_comm]
  have shiftedSummable : Summable fun index =>
      (restartBarrierSlope initial (offset + index))⁻¹ := by
    exact (summable_halfIndexSquare.mul_left coefficientFloor⁻¹
      ).of_nonneg_of_le
        (fun index => inv_nonneg.mpr
          (restartBarrierSlope_pos initial (offset + index)).le)
        shiftedMajorant
  rw [← summable_nat_add_iff (f := fun index =>
    (restartBarrierSlope initial index)⁻¹) offset]
  simpa only [Nat.add_comm] using shiftedSummable

/-! ## Exact reciprocal-barrier clock fold -/

/-- The canonical cube majorant gives a fully explicit positive lower bound
for the same successor clock.  This is the quantitative source mouth needed
to compare a scale-relative action rate with a retained cell deficit. -/
theorem explicitDurationLower_div_two_lt_successorContactTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    sourceOwnedWholeStateDurationLower nu
          (restartCoefficientCeiling initial stage) / 2 <
      (run initial (stage + 1)).contact.time.1 := by
  have lowerLe :
      sourceOwnedWholeStateDurationLower nu
          (restartCoefficientCeiling initial stage) ≤
        wholeRestartDuration (run initial stage).contact := by
    change
      sourceOwnedWholeStateDurationLower nu
          (wholeRestartCoefficientCeiling (run initial stage).contact) ≤
        sourceOwnedWholeStateDuration nu
          (wholeRestartCoefficientCeiling (run initial stage).contact)
    exact sourceOwnedWholeStateDurationLower_le nu _
  have late := run_contact_time_half_duration_lt initial (stage + 1)
  change
    wholeRestartDuration (run initial stage).contact / 2 <
      (run initial stage).nextContact.time.1 at late
  change
    sourceOwnedWholeStateDurationLower nu
          (restartCoefficientCeiling initial stage) / 2 <
      (run initial stage).nextContact.time.1
  linarith

/-- Polynomially explicit version of the same late-clock lower bound.  Its
only scale dependence is the generated seventh-order denominator. -/
theorem explicitSeventhDurationLower_div_two_lt_successorContactTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    sourceOwnedWholeStateSeventhDurationLower nu
          (restartCoefficientCeiling initial stage) / 2 <
      (run initial (stage + 1)).contact.time.1 := by
  have lowerLe :
      sourceOwnedWholeStateSeventhDurationLower nu
          (restartCoefficientCeiling initial stage) ≤
        wholeRestartDuration (run initial stage).contact := by
    change
      sourceOwnedWholeStateSeventhDurationLower nu
          (wholeRestartCoefficientCeiling (run initial stage).contact) ≤
        sourceOwnedWholeStateDuration nu
          (wholeRestartCoefficientCeiling (run initial stage).contact)
    exact sourceOwnedWholeStateSeventhDurationLower_le nu _
      (wholeRestartCoefficientCeiling_pos _).le
  have late := run_contact_time_half_duration_lt initial (stage + 1)
  change
    wholeRestartDuration (run initial stage).contact / 2 <
      (run initial stage).nextContact.time.1 at late
  change
    sourceOwnedWholeStateSeventhDurationLower nu
          (restartCoefficientCeiling initial stage) / 2 <
      (run initial stage).nextContact.time.1
  linarith

/-- The late-half selector gives the sharp lower comparison between the
reciprocal source barrier and the actual successor clock. -/
theorem reciprocalBarrier_div_four_lt_successorContactTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (restartBarrierSlope initial stage)⁻¹ / 4 <
      (run initial (stage + 1)).contact.time.1 := by
  let edge := sourceGeneratedNativeTemporalActionCouplingAt initial stage
  have lateClock := edge.late_clock
  rw [sourceGeneratedNativeTemporalActionCouplingAt_clock,
    sourceGeneratedNativeTemporalActionCouplingAt_horizon] at lateClock
  calc
    (restartBarrierSlope initial stage)⁻¹ / 4 =
        (1 / (2 * restartBarrierSlope initial stage)) / 2 := by
      have barrierNe := (restartBarrierSlope_pos initial stage).ne'
      field_simp
      ring
    _ < (run initial (stage + 1)).contact.time.1 := lateClock

/-- The exact generated horizon gives the sharp upper comparison between the
actual successor clock and the reciprocal source barrier. -/
theorem successorContactTime_le_reciprocalBarrier_div_two
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (run initial (stage + 1)).contact.time.1 <=
      (restartBarrierSlope initial stage)⁻¹ / 2 := by
  let edge := sourceGeneratedNativeTemporalActionCouplingAt initial stage
  have clockWithin := edge.clock_within
  rw [sourceGeneratedNativeTemporalActionCouplingAt_clock,
    sourceGeneratedNativeTemporalActionCouplingAt_horizon] at clockWithin
  calc
    (run initial (stage + 1)).contact.time.1 <=
        1 / (2 * restartBarrierSlope initial stage) := clockWithin
    _ = (restartBarrierSlope initial stage)⁻¹ / 2 := by
      have barrierNe := (restartBarrierSlope_pos initial stage).ne'
      field_simp

/-- The actual successor clock is no larger than the reciprocal source
barrier.  This deliberately keeps a non-sharp factor two so it can serve as
a direct nonnegative-series majorant. -/
theorem successorContactTime_le_reciprocalBarrier
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (run initial (stage + 1)).contact.time.1 <=
      (restartBarrierSlope initial stage)⁻¹ := by
  have sharp :=
    successorContactTime_le_reciprocalBarrier_div_two initial stage
  have reciprocalNonneg :
      0 <= (restartBarrierSlope initial stage)⁻¹ :=
    inv_nonneg.mpr (restartBarrierSlope_pos initial stage).le
  calc
    (run initial (stage + 1)).contact.time.1 <=
        (restartBarrierSlope initial stage)⁻¹ / 2 := sharp
    _ <= (restartBarrierSlope initial stage)⁻¹ := by
      linarith

/-- Late-half selection supplies the reverse domination: one reciprocal
barrier quantum is strictly below four actual successor-clock quanta. -/
theorem reciprocalBarrier_lt_four_mul_successorContactTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (restartBarrierSlope initial stage)⁻¹ <
      4 * (run initial (stage + 1)).contact.time.1 := by
  have sharp :=
    reciprocalBarrier_div_four_lt_successorContactTime initial stage
  linarith

/-- The nondegenerate scale/horizon projection identifies successor-clock
summability exactly with reciprocal-barrier summability. -/
theorem summable_successorContactTime_iff_reciprocalBarrier
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Summable (fun stage =>
      (run initial (stage + 1)).contact.time.1) ↔
      Summable (fun stage =>
        (restartBarrierSlope initial stage)⁻¹) := by
  constructor
  · intro clockSummable
    exact (clockSummable.mul_left 4).of_nonneg_of_le
      (fun stage =>
        inv_nonneg.mpr (restartBarrierSlope_pos initial stage).le)
      (fun stage =>
        (reciprocalBarrier_lt_four_mul_successorContactTime
          initial stage).le)
  · intro barrierSummable
    exact barrierSummable.of_nonneg_of_le
      (fun stage => (run_contact_time_pos initial (stage + 1)).le)
      (successorContactTime_le_reciprocalBarrier initial)

/-- Adding back the single source-selected initial contact does not change
summability, so the complete actual clock trace has the same exact test. -/
theorem summable_contactTime_iff_reciprocalBarrier
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Summable (fun stage => (run initial stage).contact.time.1) ↔
      Summable (fun stage =>
        (restartBarrierSlope initial stage)⁻¹) := by
  rw [← summable_successorContactTime_iff_reciprocalBarrier initial]
  exact (summable_nat_add_iff (f := fun stage =>
    (run initial stage).contact.time.1) 1).symm

/-- A source-generated immediate-settlement law for the total emitter closes
the full clock even when an edge first emits a retained residual.  The
residual edge and its settling edge together pay one scale cell. -/
theorem contactTime_summable_of_immediateCellSettlement
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (immediate : ∀ index : Nat,
      (runCellStanding initial index).IsImmediatelySettled) :
    Summable fun stage => (run initial stage).contact.time.1 :=
  (summable_contactTime_iff_reciprocalBarrier initial).2
    (summable_reciprocalBarrier_of_halfIndex_level_growth initial
      (fun index => by
        simpa only [restartCoefficientLevelNat] using
          index_div_two_le_runCoefficientLevel_of_immediateSettlement
            initial immediate index))

/-- A source theorem making the actual quantized ceiling faithful/injective
therefore closes the complete native contact-time row with no clock selector,
future branch, or summability certificate in the source mouth. -/
theorem contactTime_summable_of_restartCoefficientCeiling_injective
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (injective : Function.Injective (restartCoefficientCeiling initial)) :
    Summable fun stage => (run initial stage).contact.time.1 :=
  (summable_contactTime_iff_reciprocalBarrier initial).2
    (summable_reciprocalBarrier_of_restartCoefficientCeiling_injective
      initial injective)

/-- Direct contact-clock consumer retaining the positive amplitude generated
by a scale-relative residence law. -/
theorem contactTime_summable_of_scaled_thirteenHalf_scale_growth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (amplitude : Real)
    (amplitudePos : 0 < amplitude)
    (growth : ∀ index : Nat,
      amplitude * (((index + 1 : Nat) : Real) ^ (2 / 13 : Real)) ≤
        restartCoefficientCeiling initial index) :
    Summable fun stage => (run initial stage).contact.time.1 :=
  (summable_contactTime_iff_reciprocalBarrier initial).2
    (summable_reciprocalBarrier_of_scaled_thirteenHalf_scale_growth
      initial amplitude amplitudePos growth)

/-- The complete algebraic residence fold.  A same-occurrence physical mass
debit of order `scale⁻¹¹ᐟ²` generates its own scale recurrence and closes the
actual contact clock; no recurrence or summability witness is separately
accepted. -/
theorem contactTime_summable_of_scaleRelativeMassDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (charge : Real)
    (chargePos : 0 < charge)
    (debit : ∀ index : Nat,
      charge /
          (restartPhysicalVorticityMass initial index + 1) ^
            (11 / 2 : Real) ≤
        restartPhysicalVorticityMass initial (index + 1) -
          restartPhysicalVorticityMass initial index) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  obtain ⟨amplitude, amplitudePos, growth⟩ :=
    scaled_thirteenHalf_scale_growth_of_massDebit
      initial charge chargePos debit
  exact contactTime_summable_of_scaled_thirteenHalf_scale_growth
    initial amplitude amplitudePos growth

/-- Direct unit-normalized contact-clock consumer for the scale-relative
residence exponent.  The final source theorem will generate `growth`; this
conditional theorem is the exact algebraic fold and carries no branch or
contact selector. -/
theorem contactTime_summable_of_thirteenHalf_scale_growth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (growth : ∀ index : Nat,
      (((index + 1 : Nat) : Real) ^ (2 / 13 : Real)) ≤
        restartCoefficientCeiling initial index) :
    Summable fun stage => (run initial stage).contact.time.1 :=
  (summable_contactTime_iff_reciprocalBarrier initial).2
    (summable_reciprocalBarrier_of_thirteenHalf_scale_growth
      initial growth)

end
end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
end NavierStokes
end SaturationMonoid
