import H0mework.Versions.V2.Arithmetic.BurnolPhysical.QuarterMellinAdditiveEvenRechart
import H0mework.Versions.V2.Arithmetic.MellinProjection.PaBoundaryCommutator
import H0mework.Versions.V2.Arithmetic.RiemannSpectral.ClozelBurnolPaZeroObservation

/-!
# Modified-WeakFE unit physical Mellin read

The selected and reversal modified-WeakFE units have literal additive
Mellin read `1/4` after the reciprocal-square source rechart.  Projection to
the actual even Burnol face is then exposed as one explicit Mellin-read
defect.  No evaluator nonvanishing or defect cancellation is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex MeasureTheory Set
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open scoped InnerProductSpace

noncomputable section

theorem quarterMellinAdditivePositiveRechartRaw_mellin
    (coordinate : ℂ)
    (value : QuarterMellinL2Test (coordinate / 2)) :
    mellin (quarterMellinAdditivePositiveRechartRaw value)
        (1 - coordinate) =
      (1 / 4 : ℂ) *
        quarterMellinL2Functional (coordinate / 2) value := by
  unfold quarterMellinAdditivePositiveRechartRaw
    quarterMellinL2Functional
  rw [mellin_const_smul, mellin_cpow_smul, mellin_comp_rpow]
  norm_num [smul_eq_mul, abs_of_nonpos]
  ring_nf

theorem quarterMellinAdditiveEvenRechartRaw_mellin
    (coordinate : ℂ)
    (value : QuarterMellinL2Test (coordinate / 2)) :
    mellin (quarterMellinAdditiveEvenRechartRaw value)
        (1 - coordinate) =
      (1 / 4 : ℂ) *
        quarterMellinL2Functional (coordinate / 2) value := by
  rw [show mellin (quarterMellinAdditiveEvenRechartRaw value)
      (1 - coordinate) =
      mellin (quarterMellinAdditivePositiveRechartRaw value)
        (1 - coordinate) by
    unfold mellin
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
    rw [quarterMellinAdditiveEvenRechartRaw, abs_of_pos positive]]
  exact quarterMellinAdditivePositiveRechartRaw_mellin coordinate value

theorem selectedSourceModifiedUnit_additiveRechart_mellin_eq_quarter
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    mellin (quarterMellinAdditiveEvenRechartRaw
        (selectedSourceModifiedUnitQuarterTest observation nontrivial))
        (1 - observation.coordinate) = (1 / 4 : ℂ) := by
  have source := quarterMellinAdditiveEvenRechartRaw_mellin
    observation.coordinate
    (selectedSourceModifiedUnitQuarterTest observation nontrivial)
  change mellin (quarterMellinAdditiveEvenRechartRaw
      (selectedSourceModifiedUnitQuarterTest observation nontrivial))
      (1 - observation.coordinate) =
    (1 / 4 : ℂ) *
      quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation)
        (selectedSourceModifiedUnitQuarterTest observation nontrivial) at source
  rw [selectedSourceModifiedUnitQuarterTest_functional_one] at source
  norm_num at source ⊢
  exact source

theorem reversalSourceModifiedUnit_additiveRechart_mellin_eq_quarter
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    mellin (quarterMellinAdditiveEvenRechartRaw
        (reversalSourceModifiedUnitQuarterTest observation nontrivial))
        (1 - coordinateReversal observation.coordinate) =
      (1 / 4 : ℂ) := by
  have source := quarterMellinAdditiveEvenRechartRaw_mellin
    (coordinateReversal observation.coordinate)
    (reversalSourceModifiedUnitQuarterTest observation nontrivial)
  change mellin (quarterMellinAdditiveEvenRechartRaw
      (reversalSourceModifiedUnitQuarterTest observation nontrivial))
      (1 - coordinateReversal observation.coordinate) =
    (1 / 4 : ℂ) *
      quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation)
        (reversalSourceModifiedUnitQuarterTest observation nontrivial) at source
  rw [reversalSourceModifiedUnitQuarterTest_functional_one] at source
  norm_num at source ⊢
  exact source

/-- Actual physical image obtained by orthogonally projecting the literal
even additive rechart. -/
def quarterMellinAdditiveProjectedPhysicalState {z : ℂ}
    (value : QuarterMellinL2Test z) : BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection (quarterMellinAdditiveEvenRechart value)

theorem quarterMellinAdditiveProjectedPhysicalState_evaluator_eq_inner
    (coordinate : BurnolCompletedMellinCoordinate)
    {z : ℂ} (value : QuarterMellinL2Test z) :
    burnolCompletedMellinEvaluator coordinate
        (quarterMellinAdditiveProjectedPhysicalState value) =
      inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
        (quarterMellinAdditiveEvenRechart value) := by
  rw [← burnolCompletedMellinRieszVector_readback]
  unfold quarterMellinAdditiveProjectedPhysicalState
    burnolEvenAmbientProjection
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_left
      (burnolCompletedMellinRieszVector coordinate)
      (quarterMellinAdditiveEvenRechart value)

/-- Direct consumer: for the selected unit, the desired projected evaluator
read is equivalent to vanishing of the exact raw-Mellin minus projected-Riesz
read.  The right-hand zero is a remaining conclusion, never an input. -/
theorem selectedSourceModifiedUnit_projectedEvaluator_eq_quarter_iff
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    let observation := burnolPaZeroObservation coordinate zero
    let nontrivial := burnolPaZeroObservation_nontrivial coordinate zero
    let unit := selectedSourceModifiedUnitQuarterTest observation nontrivial
    burnolCompletedMellinEvaluator coordinate
        (quarterMellinAdditiveProjectedPhysicalState unit) =
        (1 / 4 : ℂ) ↔
      mellin (quarterMellinAdditiveEvenRechartRaw unit)
          (1 - coordinate.value) -
        inner ℂ
          (burnolCompletedMellinRieszVector coordinate : BurnolL2)
          (quarterMellinAdditiveEvenRechart unit) = 0 := by
  dsimp only
  have rawRead := selectedSourceModifiedUnit_additiveRechart_mellin_eq_quarter
    (burnolPaZeroObservation coordinate zero)
    (burnolPaZeroObservation_nontrivial coordinate zero)
  have rawRead' :
      mellin (quarterMellinAdditiveEvenRechartRaw
          (selectedSourceModifiedUnitQuarterTest
            (burnolPaZeroObservation coordinate zero)
            (burnolPaZeroObservation_nontrivial coordinate zero)))
          (1 - coordinate.value) = (1 / 4 : ℂ) := by
    simpa [burnolPaZeroObservation] using rawRead
  rw [rawRead']
  rw [← quarterMellinAdditiveProjectedPhysicalState_evaluator_eq_inner]
  simp only [sub_eq_zero]
  exact eq_comm

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
