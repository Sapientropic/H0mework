import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ExteriorFourierSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WindowLog

open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

open private fourier_l2_raw from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ExteriorFourierSource
open private seedFourierRaw seed_fourier_inverse_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Q" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "F" => fourierL2

/-- The original quarter window, carried through the full Fourier isometry. -/
def quarterFourierCut : BurnolL2 →L[ℂ] BurnolL2 :=
  fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (burnolQuarterZeroExtension.comp (burnolQuarterRestriction.comp
      fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem quarterFourierCut_apply (v : BurnolL2) :
    quarterFourierCut v = F (E (Q (fourierL2.symm v))) := rfl

def quarterSincKernel (x y : ℝ) : ℂ := star (seedFourierRaw (y - x))

private def positivePhase (x t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * inner ℝ t x : ℝ) : ℂ) * Complex.I)

private def negativePhase (x t : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * inner ℝ t x : ℝ) : ℂ) * Complex.I)

private theorem positive_phase_norm (x t : ℝ) : ‖positivePhase x t‖ = 1 := by
  rw [positivePhase, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem phase_conj (x t : ℝ) : star (positivePhase x t) = negativePhase x t := by
  unfold positivePhase negativePhase
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem phase_shift (x y t : ℝ) :
    negativePhase y t * positivePhase x t = negativePhase (y - x) t := by
  simp only [negativePhase, positivePhase, ← Complex.exp_add, inner_sub_right]
  congr 1
  push_cast
  ring

private def modulatedConstant (x t : ℝ) : ℂ := positivePhase x t * intervalConstant q t

private theorem modulation_memLp (x : ℝ) : MemLp (modulatedConstant x) 2 μq := by
  have phaseContinuous : Continuous (positivePhase x) := by
    unfold positivePhase
    fun_prop
  apply (Lp.memLp (intervalConstant q)).norm.mono'
    (phaseContinuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (intervalConstant q)))
  filter_upwards with t
  change ‖modulatedConstant x t‖ ≤ ‖intervalConstant q t‖
  simp [modulatedConstant, positive_phase_norm]

private def modulationState (x : ℝ) : BurnolQuarterIntervalL2 :=
  (modulation_memLp x).toLp (modulatedConstant x)

private def modulationKet (x : ℝ) : BurnolL2 := E (modulationState x)

private theorem modulation_state_read (x : ℝ) :
    (modulationState x : ℝ → ℂ) =ᵐ[μq] modulatedConstant x :=
  (modulation_memLp x).coeFn_toLp

private theorem modulation_truncated_read (x y : ℝ) :
    burnolTruncatedFourierRaw (modulationState x) y = seedFourierRaw (y - x) := by
  change burnolRadiusTruncatedFourierRaw q (modulationState x) y =
    burnolRadiusTruncatedFourierRaw q (intervalConstant q) (y - x)
  simp only [burnolRadiusTruncatedFourierRaw, Real.vector_fourierIntegral_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [modulation_state_read x] with t actual
  change negativePhase y t * modulationState x t = negativePhase (y - x) t * intervalConstant q t
  rw [actual, modulatedConstant, ← mul_assoc, phase_shift]

private theorem modulation_fourier_raw (x : ℝ) :
    (F (modulationKet x) : ℝ → ℂ) =ᵐ[volume] fun y => seedFourierRaw (y - x) := by
  have compact : Integrable (modulationKet x : ℝ → ℂ) volume :=
    (burnolQuarterZeroExtensionRaw_integrable (modulationState x)).congr
      (burnolQuarterZeroExtension_coe (modulationState x)).symm
  filter_upwards [fourier_l2_raw (modulationKet x) compact] with y actual
  calc
    _ = 𝓕 (modulationKet x : ℝ → ℂ) y := actual
    _ = 𝓕 ((symmetricInterval q).indicator fun t => modulationState x t) y :=
      Real.fourier_congr_ae (burnolQuarterZeroExtension_coe (modulationState x)) y
    _ = burnolTruncatedFourierRaw (modulationState x) y :=
      (burnolTruncatedFourierRaw_eq_fourier_zeroExtension (modulationState x) y).symm
    _ = _ := modulation_truncated_read x y

private theorem truncated_pair (u : BurnolL2) (x : ℝ) :
    burnolTruncatedFourierRaw (Q u) x = inner ℂ (modulationState x) (Q u) := by
  change burnolRadiusTruncatedFourierRaw q (Q u) x = _
  simp only [burnolRadiusTruncatedFourierRaw, Real.vector_fourierIntegral_eq_integral_exp_smul, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modulation_state_read x, intervalConstant_coeFn q] with t actual constant
  change negativePhase x t * (Q u) t = inner ℂ (modulationState x t) ((Q u) t)
  rw [actual, modulatedConstant, constant, mul_one, RCLike.inner_apply']
  change _ = star (positivePhase x t) * (Q u) t
  rw [phase_conj]

private theorem row_pairing_raw (v : BurnolL2) (x : ℝ) :
    (fun y : ℝ => inner ℂ (F (modulationKet x) y) (v y)) =ᵐ[volume]
      fun y => quarterSincKernel x y * v y := by
  filter_upwards [modulation_fourier_raw x] with y actual
  rw [actual, quarterSincKernel]
  exact RCLike.inner_apply' _ _

theorem quarter_sinc_integrable_row (v : BurnolL2) (x : ℝ) :
    Integrable (fun y : ℝ => quarterSincKernel x y * v y) volume :=
  (L2.integrable_inner (𝕜 := ℂ) (F (modulationKet x)) v).congr (row_pairing_raw v x)

private theorem truncated_fourier_row (v : BurnolL2) (x : ℝ) :
    burnolTruncatedFourierRaw (Q (fourierL2.symm v)) x =
      ∫ y : ℝ, quarterSincKernel x y * v y := by
  calc
    _ = inner ℂ (modulationState x) (Q (fourierL2.symm v)) := truncated_pair _ x
    _ = inner ℂ (modulationKet x) (fourierL2.symm v) :=
      (ContinuousLinearMap.adjoint_inner_left Q (fourierL2.symm v) (modulationState x)).symm
    _ = inner ℂ (F (modulationKet x)) v := (fourierL2.inner_map_eq_flip (modulationKet x) v).symm
    _ = _ := by
      rw [L2.inner_def]
      exact integral_congr_ae (row_pairing_raw v x)

theorem quarter_cut_raw (v : BurnolL2) :
    (quarterFourierCut v : ℝ → ℂ) =ᵐ[volume] fun x => ∫ y : ℝ, quarterSincKernel x y * v y :=
  (burnolFourierL2_zeroExtension_ae_eq_raw (Q (fourierL2.symm v))).trans
    (Eventually.of_forall (truncated_fourier_row v))

theorem quarter_sinc_kernel_bound {x y : ℝ} (distinct : x ≠ y) :
    ‖quarterSincKernel x y‖ ≤ |x - y|⁻¹ := by
  rw [quarterSincKernel, norm_star, abs_sub_comm x y]
  exact seed_fourier_inverse_bound (y - x) (sub_ne_zero.mpr distinct.symm)

end OriginalGamma.Source.WindowLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
