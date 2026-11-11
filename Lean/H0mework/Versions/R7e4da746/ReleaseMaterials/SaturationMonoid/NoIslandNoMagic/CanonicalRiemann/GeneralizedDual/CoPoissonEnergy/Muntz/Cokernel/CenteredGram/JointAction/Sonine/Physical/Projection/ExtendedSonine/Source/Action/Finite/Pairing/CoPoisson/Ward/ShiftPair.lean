import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticAdjoint
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.HKernelRead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualShell

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ShiftPair

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalPaPhysicalGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private def ambient (shift : ℝ) : Hq →L[ℂ] Hq := burnolQuarterRestriction.comp
  ((burnolMultiplicativeDilation shift).toContinuousLinearEquiv.toContinuousLinearMap.comp burnolQuarterZeroExtension)

/-- The original restriction, unitary dilation, extension and mean projection define both sides independently. -/
def forward : M →L[ℂ] M := Constructor.zeroMean.comp ((ambient (Real.log 2)).comp
  (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

def reverse : M →L[ℂ] M := Constructor.zeroMean.comp ((ambient (-Real.log 2)).comp
  (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

private theorem ambient_pair (shift : ℝ) (left right : Hq) :
    inner ℂ (ambient shift left) right = inner ℂ left (ambient (-shift) right) := by
  have first : inner ℂ (ambient shift left) right = inner ℂ
      (burnolMultiplicativeDilation shift (burnolQuarterZeroExtension left)) (burnolQuarterZeroExtension right) :=
    (ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _).symm
  have second := (burnolMultiplicativeDilation shift).inner_map_eq_flip
    (burnolQuarterZeroExtension left) (burnolQuarterZeroExtension right)
  rw [← burnolMultiplicativeDilation_neg_eq_symm] at second
  rw [first, second]
  exact ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _

theorem adjoint_pair (left right : M) : inner ℂ (forward left) right = inner ℂ left (reverse right) := by
  change inner ℂ (Constructor.zeroMean (ambient (Real.log 2) (left : Hq))) right =
    inner ℂ left (Constructor.zeroMean (ambient (-Real.log 2) (right : Hq)))
  simp only [Constructor.zeroMean, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact ambient_pair _ _ _

theorem adjoint_eq : forward.adjoint = reverse := by
  apply ContinuousLinearMap.ext
  intro right
  apply ext_inner_left ℂ
  intro left
  have actual : inner ℂ left (forward.adjoint right) = inner ℂ (forward left) right :=
    ContinuousLinearMap.adjoint_inner_right forward _ _
  exact actual.trans (adjoint_pair left right)

private theorem reverse_constant : ambient (-Real.log 2) (intervalConstant q) =
    ((Real.sqrt 2 : ℂ) * (1 / 2 : ℂ)) • intervalConstant q := by
  have source := SingularCounting.counting_constant 2 (by norm_num)
  have scale : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have multiplied := congrArg ((Real.sqrt 2 : ℂ) • ·) source
  simpa only [ambient, ContinuousLinearMap.comp_apply, InverseAction.countingWindow, smul_smul, mul_inv_cancel₀ scale, one_smul, Complex.ofReal_ofNat, one_div] using! multiplied

private theorem forward_mean_zero (value : M) : burnolQuarterMeanCoefficient (ambient (Real.log 2) (value : Hq)) = 0 := by
  have zero : inner ℂ (intervalConstant q) (value : Hq) = 0 :=
    (Submodule.mem_orthogonal _ _).mp value.property _ (Submodule.mem_span_singleton_self _)
  have paired := ambient_pair (-Real.log 2) (intervalConstant q) (value : Hq)
  rw [neg_neg, reverse_constant, inner_smul_left, zero, mul_zero] at paired
  unfold burnolQuarterMeanCoefficient
  rw [← paired, zero_div]

theorem forward_read (value : M) : (forward value : Hq) = ambient (Real.log 2) (value : Hq) := by
  change (Constructor.zeroMean (ambient (Real.log 2) (value : Hq)) : Hq) = _
  rw [Constructor.zeroMean_read, forward_mean_zero, zero_smul, sub_zero]

private theorem extension_support (value : Hq) :
    originalPhysicalCutoff (2 * q) (burnolQuarterZeroExtension value) = burnolQuarterZeroExtension value := by
  apply OriginalRieszFiniteColumns.cutoff_eq_self_of_ae_zero
  filter_upwards [burnolQuarterZeroExtension_coe value] with x read outside
  rw [read, indicator_of_notMem]
  intro inside
  apply outside
  exact ⟨by linarith [inside.1], by linarith [inside.2]⟩

theorem forward_extension (value : M) :
    burnolQuarterZeroExtension (forward value : Hq) =
      burnolMultiplicativeDilation (Real.log 2) (burnolQuarterZeroExtension (value : Hq)) := by
  rw [forward_read]
  change originalPhysicalCutoff q (burnolMultiplicativeDilation (Real.log 2)
    (burnolQuarterZeroExtension (value : Hq))) = _
  rw [originalPhysicalCutoff_dilation, Real.exp_log (by norm_num : (0 : ℝ) < 2), extension_support]

private theorem extension_pair (left right : Hq) :
    inner ℂ (burnolQuarterZeroExtension left) (burnolQuarterZeroExtension right) = inner ℂ left right := by
  have actual : inner ℂ (burnolQuarterZeroExtension left) (burnolQuarterZeroExtension right) =
      inner ℂ left (burnolQuarterRestriction (burnolQuarterZeroExtension right)) :=
    ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _
  rwa [burnolQuarterRestriction_zeroExtension] at actual

theorem inner_map (left right : M) : inner ℂ (forward left) (forward right) = inner ℂ left right := by
  change inner ℂ (forward left : Hq) (forward right : Hq) = inner ℂ (left : Hq) (right : Hq)
  rw [← extension_pair, forward_extension, forward_extension,
    (burnolMultiplicativeDilation (Real.log 2)).inner_map_map, extension_pair]

theorem isometry (value : M) : ‖forward value‖ = ‖value‖ := by
  have actual := inner_map value value
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at actual
  have square : ‖forward value‖ ^ 2 = ‖value‖ ^ 2 := by exact_mod_cast actual
  nlinarith [norm_nonneg (forward value), norm_nonneg value]

theorem reverse_forward (value : M) : reverse (forward value) = value := by
  apply ext_inner_left ℂ
  intro test
  rw [← adjoint_pair, inner_map]

private theorem ambient_fourier (value : Hq) :
    ambient (-Real.log 2) (burnolTruncatedFourier value) =
      burnolQuarterRestriction (burnolMultiplicativeDilation (-Real.log 2) (fourierL2 (burnolQuarterZeroExtension value))) := by
  have actual := ArithmeticAdjoint.counting_fourier 2 (by norm_num) value
  have scalar : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have multiplied := congrArg ((Real.sqrt 2 : ℂ) • ·) actual
  simpa only [ambient, ContinuousLinearMap.comp_apply, InverseAction.countingWindow, smul_smul, mul_inv_cancel₀ scalar, one_smul] using! multiplied

/-- The single reverse isometry intertwines the original S with its separately constructed adjoint. -/
theorem fourier_intertwining (value : M) :
    burnolMeanZeroTruncatedFourier (forward value) = reverse (burnolMeanZeroTruncatedFourier value) := by
  have first : burnolMeanZeroTruncatedFourier (forward value) =
      Constructor.zeroMean (ambient (-Real.log 2) (burnolTruncatedFourier (value : Hq))) := by
    change Constructor.zeroMean (burnolQuarterRestriction (fourierL2
      (burnolQuarterZeroExtension (forward value : Hq)))) = _
    rw [forward_extension, fourierL2_burnolMultiplicativeDilation, ambient_fourier]
  rw [first]
  change Constructor.zeroMean (ambient (-Real.log 2) (burnolTruncatedFourier (value : Hq))) =
    Constructor.zeroMean (ambient (-Real.log 2) (burnolMeanZeroTruncatedFourier value : Hq))
  have centered : (burnolMeanZeroTruncatedFourier value : Hq) = burnolTruncatedFourier (value : Hq) -
      burnolQuarterMeanCoefficient (burnolTruncatedFourier (value : Hq)) • intervalConstant q :=
    Constructor.zeroMean_read _
  rw [centered, map_sub, map_smul, map_sub, map_smul, reverse_constant, map_smul, Constructor.zeroMean_constant,
    smul_zero, smul_zero, sub_zero]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ShiftPair
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
