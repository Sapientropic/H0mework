import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteSource

set_option autoImplicit false
set_option Elab.async false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open Complex BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open scoped InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier

theorem meanZeroDilation_zero (value : M) : meanZeroDilation 0 value = value := by
  apply Subtype.ext
  have whole := congrArg burnolQuarterRestriction (inward_extension 0 le_rfl value)
  simpa only [burnolMultiplicativeDilation_zero, burnolQuarterRestriction_zeroExtension] using whole

theorem sourceCommutator_zero (value : M) : sourceCommutator 0 value = 0 := by
  change meanZeroDilation 0 (S value) - meanZeroDilation (-0) (S value) = 0
  rw [neg_zero, sub_self]

theorem outwardExterior_zero (value : M) : outwardExterior 0 value = 0 := by
  change burnolMultiplicativeDilation (-0) (burnolQuarterZeroExtension (value : Hq)) -
    burnolQuarterZeroExtension (burnolQuarterRestriction
      (burnolMultiplicativeDilation (-0) (burnolQuarterZeroExtension (value : Hq)))) = 0
  rw [neg_zero, burnolMultiplicativeDilation_zero, burnolQuarterRestriction_zeroExtension, sub_self]

theorem outwardMean_zero (value : M) : outwardMean 0 value = 0 := by
  change burnolQuarterMeanCoefficient (burnolQuarterRestriction
    (burnolMultiplicativeDilation (-0) (burnolQuarterZeroExtension (value : Hq)))) = 0
  rw [neg_zero, burnolMultiplicativeDilation_zero, burnolQuarterRestriction_zeroExtension]
  exact Constructor.mean_zero value

theorem fullWindowLoss_zero (value : M) : fullWindowLoss 0 value = 0 := by
  rw [fullWindowLoss, outwardExterior_zero, outwardMean_zero, zero_smul, add_zero]

/-- The override preserves the original source pair, both drives and both loss feet. -/
theorem actual_B_source_zero :
    sourceDrive 0 = Response.eta ∧ sourceDriveV 0 = S Response.eta ∧
    sourceFirst 0 = Response.u ∧ sourceSecond 0 = Response.v ∧
    sourceVFirst 0 = Response.v ∧ sourceVSecond 0 = Response.u - Response.eta ∧
    fullWindowLoss 0 Response.u = 0 ∧ fullWindowLoss 0 Response.v = 0 := by
  have drive : sourceDrive 0 = Response.eta := by
    simp only [sourceDrive, meanZeroDilation_zero, sourceCommutator_zero, map_zero, add_zero]
  have driveV : sourceDriveV 0 = S Response.eta := by
    simp only [sourceDriveV, meanZeroDilation_zero, sourceCommutator_zero, map_zero, add_zero]
  have first := sourceFirst_actual 0 le_rfl
  rw [meanZeroDilation_zero] at first
  have second := sourceSecond_actual 0 le_rfl
  rw [neg_zero, meanZeroDilation_zero] at second
  have vfirst := sourceVFirst_actual 0 le_rfl
  rw [meanZeroDilation_zero] at vfirst
  have vsecond := sourceVSecond_actual 0 le_rfl
  rw [neg_zero, meanZeroDilation_zero, meanZeroDilation_zero] at vsecond
  have vsecondRead : sourceVSecond 0 = Response.u - Response.eta := by
    linear_combination (norm := module) vsecond
  exact ⟨drive, driveV, first, second, vfirst, vsecondRead,
    fullWindowLoss_zero Response.u, fullWindowLoss_zero Response.v⟩

theorem actual_f0_source_zero (coordinate : BurnolCompletedMellinCoordinate) :
    f0MinusSource coordinate 0 = regularForcing coordinate 0 ∧
      f0PlusSource coordinate 0 = regularForcing coordinate 0 := by
  constructor
  · simpa only [neg_zero, burnolMultiplicativeDilation_zero] using
      (forcing0_backward_source coordinate 0 le_rfl).symm
  · simpa only [burnolMultiplicativeDilation_zero] using
      (forcing0_forward_source coordinate 0 le_rfl).symm

/-- These deletion controls remove only the full outward loss, keeping the original contact. -/
def f0MinusWithoutWindowLoss (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  fourierL2 (burnolQuarterZeroExtension (sourceFirst h : Hq)) -
    burnolQuarterZeroExtension (sourceSecond h : Hq) +
      (1/2 - sourceRate coordinate) • burnolMultiplicativeDilation (-h) ConstantDual.seed

def f0PlusWithoutWindowLoss (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  fourierL2 (burnolQuarterZeroExtension
    (sourceVSecond h + meanZeroDilation (-h) Response.eta : Hq)) -
    burnolQuarterZeroExtension (sourceVFirst h : Hq) +
      (1/2 - sourceRate coordinate) • burnolMultiplicativeDilation h ConstantDual.seed

theorem delete_minus_loss_actual (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    f0MinusWithoutWindowLoss coordinate h -
      burnolMultiplicativeDilation (-h) (regularForcing coordinate 0) = fullWindowLoss h Response.v := by
  rw [forcing0_backward_source coordinate h nonnegative]
  unfold f0MinusWithoutWindowLoss f0MinusSource
  module

theorem delete_plus_loss_actual (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    f0PlusWithoutWindowLoss coordinate h -
      burnolMultiplicativeDilation h (regularForcing coordinate 0) = -fourierL2 (fullWindowLoss h Response.u) := by
  rw [forcing0_forward_source coordinate h nonnegative]
  unfold f0PlusWithoutWindowLoss f0PlusSource
  module

theorem delete_minus_loss_originalK_price (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (generatedK coordinate) (f0MinusWithoutWindowLoss coordinate h) -
      inner ℂ (generatedK coordinate)
        (burnolMultiplicativeDilation (-h) (regularForcing coordinate 0)) =
          inner ℂ (generatedK coordinate) (fullWindowLoss h Response.v) := by
  rw [← inner_sub_right, delete_minus_loss_actual coordinate h nonnegative]

theorem delete_plus_loss_originalK_price (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (generatedK coordinate) (f0PlusWithoutWindowLoss coordinate h) -
      inner ℂ (generatedK coordinate)
        (burnolMultiplicativeDilation h (regularForcing coordinate 0)) =
          -inner ℂ (generatedK coordinate) (fourierL2 (fullWindowLoss h Response.u)) := by
  rw [← inner_sub_right, delete_plus_loss_actual coordinate h nonnegative, inner_neg_right]

end
end OriginalKSourceFiniteUpdate.OriginalBFiniteAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
