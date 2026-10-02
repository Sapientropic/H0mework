import H0mework.Versions.R2.Arithmetic.MellinBoundary.StageZeroLowHighSupport

/-!
# Stage-zero low/high residual no-go

The canonical conjugate inversion is source-native but does not map the
selected normalized-low face to the reversal normalized-low face.  Their
difference is retained as an explicit proper-`L¹` residual with a nonzero
low-window coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open QRich
open CanonicalUnitArithmeticCoordinateProjectionObstruction

noncomputable section

/-- Coverage-exact deletion of the false low-to-low partner incidence. -/
theorem positiveMellinL1StarInversion_selected_ne_reversal
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1StarInversion
        (selectedStageZeroProperMellinL1 observation nontrivial) ≠
      reversalStageZeroProperMellinL1 observation nontrivial := by
  intro equality
  have lowWindowIntegralEquality := congrArg
    (fun value : PositiveMellinL1 =>
      ∫ t : ℝ in stageZeroLowWindow, (value : ℝ → ℂ) t)
    equality
  rw [starInversionSelectedStageZero_lowWindow_integral_zero,
    reversalStageZeroProperMellinL1_lowWindow_integral]
    at lowWindowIntegralEquality
  exact reversalStageZeroProperMellinL1_integral_ne_zero
    observation nontrivial lowWindowIntegralEquality.symm

def positiveMellinL1StageZeroStarInversionResidual
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PositiveMellinL1 :=
  positiveMellinL1StarInversion
      (selectedStageZeroProperMellinL1 observation nontrivial) -
    reversalStageZeroProperMellinL1 observation nontrivial

theorem positiveMellinL1StageZeroStarInversionResidual_lowWindow
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (positiveMellinL1StageZeroStarInversionResidual
        observation nontrivial : ℝ → ℂ) =ᵐ[
      volume.restrict stageZeroLowWindow]
        (fun t => -(
          reversalStageZeroProperMellinL1 observation nontrivial :
            ℝ → ℂ) t) := by
  have residualRead := Lp.coeFn_sub
    (positiveMellinL1StarInversion
      (selectedStageZeroProperMellinL1 observation nontrivial))
    (reversalStageZeroProperMellinL1 observation nontrivial)
  have selectedZero :=
    positiveMellinL1StarInversion_selected_zero_on_lowWindow
      observation nontrivial
  have windowMeasureLe :
      volume.restrict stageZeroLowWindow ≤
        volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono stageZeroLowWindow_subset_positive le_rfl
  filter_upwards
    [(ae_mono windowMeasureLe) residualRead, selectedZero]
    with t hresidual hselected
  change ((positiveMellinL1StarInversion
      (selectedStageZeroProperMellinL1 observation nontrivial) -
        reversalStageZeroProperMellinL1 observation nontrivial :
          PositiveMellinL1) : ℝ → ℂ) t = _
  rw [hresidual]
  simp only [Pi.sub_apply]
  simpa using hselected

theorem positiveMellinL1StageZeroStarInversionResidual_lowWindow_integral
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (∫ t : ℝ in stageZeroLowWindow,
        (positiveMellinL1StageZeroStarInversionResidual
          observation nontrivial : ℝ → ℂ) t) =
      -positiveMellinL1Integral
        (reversalStageZeroProperMellinL1 observation nontrivial) := by
  rw [integral_congr_ae
    (positiveMellinL1StageZeroStarInversionResidual_lowWindow
      observation nontrivial)]
  rw [integral_neg,
    reversalStageZeroProperMellinL1_lowWindow_integral]

theorem positiveMellinL1StageZeroStarInversionResidual_coordinate
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (∫ t : ℝ in stageZeroLowWindow,
        (positiveMellinL1StageZeroStarInversionResidual
          observation nontrivial : ℝ → ℂ) t) =
      -(blockQRichSuccessorScale 0 : ℂ) ^
        (-(coordinateReversal observation.coordinate / 2)) := by
  rw [positiveMellinL1StageZeroStarInversionResidual_lowWindow_integral,
    reversalStageZeroProperMellinL1_integral,
    generatedZeroReversalProperMellinReadback_eq_character]

theorem positiveMellinL1StageZeroStarInversionResidual_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1StageZeroStarInversionResidual
        observation nontrivial ≠ 0 := by
  rw [positiveMellinL1StageZeroStarInversionResidual, sub_ne_zero]
  exact positiveMellinL1StarInversion_selected_ne_reversal
    observation nontrivial

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
