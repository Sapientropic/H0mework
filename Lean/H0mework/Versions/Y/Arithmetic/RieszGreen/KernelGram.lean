import H0mework.Versions.Y.Arithmetic.RieszGreen.GapGram
import H0mework.Versions.Y.Arithmetic.RieszGreen.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex
open scoped InnerProductSpace
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "b" => burnolRieszSingleFourierSource
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "E" => burnolQuarterZeroExtension
local notation "K" => burnolCompletedMellinRieszVector

def sourceCorrection (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (E (b coordinate : BurnolQuarterIntervalL2)) -
    E (S (b coordinate) : BurnolQuarterIntervalL2)

theorem gapState_eq_kernel_add_correction (coordinate : BurnolCompletedMellinCoordinate) :
    gapState coordinate = (K coordinate : BurnolL2) + sourceCorrection coordinate := by
  rw [Kernel.original_kernel_reconstruction]
  unfold gapState sourceCorrection
  module

theorem sourceCorrection_eq_generated (coordinate : BurnolCompletedMellinCoordinate) :
    sourceCorrection coordinate = burnolAmbientEvenMeanZeroCorrection
      (burnolAmbientCompletedMellinKernelFormula coordinate) := by
  have generated := burnolCompletedMellinRieszVector_eq_resolventFormula coordinate
  change (K coordinate : BurnolL2) = gapState coordinate -
    burnolAmbientEvenMeanZeroCorrection (burnolAmbientCompletedMellinKernelFormula coordinate) at generated
  calc
    _ = gapState coordinate - (K coordinate : BurnolL2) := by
      rw [gapState_eq_kernel_add_correction]
      abel
    _ = _ := by
      rw [generated]
      abel

theorem sourceCorrection_inner_kernel_zero (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (sourceCorrection left) (K right : BurnolL2) = 0 := by
  rw [sourceCorrection_eq_generated]
  exact burnolAmbientEvenMeanZeroCorrection_inner_physical_eq_zero _ (K right)

theorem kernel_inner_sourceCorrection_zero (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (K left : BurnolL2) (sourceCorrection right) = 0 :=
  inner_eq_zero_symm.mp (sourceCorrection_inner_kernel_zero right left)

theorem quarter_extension_inner (left right : BurnolQuarterIntervalL2) :
    inner ℂ (E left) (E right) = inner ℂ left right := by
  calc
    _ = inner ℂ left (burnolQuarterRestriction (E right)) :=
      ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction (E right) left
    _ = _ := by
      change inner ℂ left (burnolRadiusRestriction q (burnolRadiusZeroExtension q right)) = _
      rw [burnolRadiusRestriction_zeroExtension]

theorem extension_fourier_pairing (left right : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (E (left : BurnolQuarterIntervalL2)) (fourierL2 (E (right : BurnolQuarterIntervalL2))) =
      inner ℂ left (S right) := by
  have raw : inner ℂ (E (left : BurnolQuarterIntervalL2)) (fourierL2 (E (right : BurnolQuarterIntervalL2))) =
      inner ℂ (left : BurnolQuarterIntervalL2) (burnolTruncatedFourier (right : BurnolQuarterIntervalL2)) :=
    ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction
      (fourierL2 (E (right : BurnolQuarterIntervalL2))) (left : BurnolQuarterIntervalL2)
  rw [raw]
  unfold burnolMeanZeroTruncatedFourier
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

theorem sourceCorrection_inner (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (sourceCorrection left) (sourceCorrection right) =
      inner ℂ (b left) (b right) - inner ℂ (S (b left)) (S (b right)) := by
  have crossed : inner ℂ (fourierL2 (E (b left : BurnolQuarterIntervalL2)))
      (E (S (b right) : BurnolQuarterIntervalL2)) = inner ℂ (S (b left)) (S (b right)) := by
    calc
      _ = star (inner ℂ (E (S (b right) : BurnolQuarterIntervalL2))
          (fourierL2 (E (b left : BurnolQuarterIntervalL2)))) := (inner_conj_symm _ _).symm
      _ = star (inner ℂ (S (b right)) (S (b left))) := by rw [extension_fourier_pairing]
      _ = _ := inner_conj_symm _ _
  unfold sourceCorrection
  rw [inner_sub_left, inner_sub_right, inner_sub_right, fourierL2.inner_map_map,
    quarter_extension_inner, crossed, extension_fourier_pairing, quarter_extension_inner]
  change (inner ℂ (b left) (b right) - inner ℂ (S (b left)) (S (b right))) -
    (inner ℂ (S (b left)) (S (b right)) - inner ℂ (S (b left)) (S (b right))) = _
  ring

/-- The actual projection subtracts the Gram of its same-inverse correction. -/
theorem kernel_source_gram (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (K left : BurnolL2) (K right : BurnolL2) =
      inner ℂ (gapState left) (gapState right) -
        (inner ℂ (b left) (b right) - inner ℂ (S (b left)) (S (b right))) := by
  rw [gapState_eq_kernel_add_correction left, gapState_eq_kernel_add_correction right,
    inner_add_left, inner_add_right, inner_add_right,
    kernel_inner_sourceCorrection_zero, sourceCorrection_inner_kernel_zero, sourceCorrection_inner]
  ring

/-- The original gap/tail and original source Green law generate the whole K Gram. -/
theorem original_kernel_gram (left right : BurnolCompletedMellinCoordinate) :
    (left.value + star right.value - 1) * inner ℂ (K left : BurnolL2) (K right : BurnolL2) =
      (1 / 2 : ℂ) * (star (Kernel.A left) * Kernel.A right -
        star (Kernel.beta left) * Kernel.beta right) := by
  rw [kernel_source_gram, mul_sub, gapState_gram, original_source_green]
  ring

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
