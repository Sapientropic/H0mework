import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.KGamma.Iterated

open Complex Filter MeasureTheory Set OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting
open private inv_weighted logSynthesis log_seed_synthesis_apply from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorStrongSource
open private reverse_synthesis_log_source radialLogSynthesis log_pair_add from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
open private seed_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.HermitianGammaTauSource
open private seedFourierRaw seedFourierLog seed_fourier_raw seed_fourier_log_pair
  seed_fourier_bound seed_fourier_inverse_bound powerProfile powerEnvelopeRaw powerEnvelopeL2
  envelope_raw envelope_norm weighted_log_power_integrable logPair_smul logPair_sub from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

local notation "q" => (1 / 4 : ℝ)
local notation "C" => ConstantDual.seed
local notation "F" => fourierL2

private theorem inverse_log_weighted :
    IntegrableOn (fun t : ℝ => Real.sqrt t * |Real.log (4 * t)| * ‖(t : ℂ)⁻¹‖) (Ioc 0 q) := by
  apply (weighted_log_power_integrable (-1 / 2) (by norm_num)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  have power : Real.sqrt t * ‖(t : ℂ)⁻¹‖ = t ^ (-1 / 2 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos inside.1, Real.sqrt_eq_rpow,
      ← Real.rpow_neg_one, ← Real.rpow_add inside.1]
    congr 1
    norm_num
  change |Real.log (4 * t)| * t ^ (-1 / 2 : ℝ) =
    Real.sqrt t * |Real.log (4 * t)| * ‖(t : ℂ)⁻¹‖
  rw [← power]
  ring

private theorem seed_inverse_log : LogPair (fourierL2.symm C) seedFourierLog := by
  rw [fourierL2_symm_eq_reflect_fourierL2, ← fourierL2_reflectL2_commute, seed_even]
  exact seed_fourier_log_pair

private def inverseSynthesisLog : BurnolL2 :=
  fourierL2.symm (logSynthesis (F seedFourierLog) -
    radialLogSynthesis (Ioc 0 q) (fun t : ℝ => (t : ℂ)⁻¹) C)

private theorem inverse_synthesis_log :
    LogPair (fourierL2.symm (logSynthesis C)) inverseSynthesisLog := by
  have paid := reverse_synthesis_log_source (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (fun t : ℝ => (t : ℂ)⁻¹) (by fun_prop) inv_weighted inverse_log_weighted
    C seedFourierLog seed_inverse_log
  change LogPair (fourierL2.symm (logSynthesis C)) inverseSynthesisLog at paid
  exact paid

private theorem log_square_power_bound (y p : ℝ) (positive : 0 < y)
    (read : |Real.log y| = 8 * (p * Real.log y)) :
    |Real.log y| ^ 2 ≤ 64 * y ^ (p * 2) := by
  have paid := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive p)
  rw [Real.log_rpow positive] at paid
  have upper : |Real.log y| ≤ 8 * y ^ p := by
    rw [read]
    linarith
  calc
    _ ≤ (8 * y ^ p) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) upper _
    _ = _ := by
      rw [mul_pow, ← Real.rpow_two (y ^ p), ← Real.rpow_mul positive.le]
      norm_num

private theorem seed_square_log_bound (x : ℝ) (nonzero : x ≠ 0) :
    ‖(Real.log |x| : ℂ) * ((Real.log |x| : ℂ) * seedFourierRaw x)‖ ≤
      64 * powerProfile |x| := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← mul_assoc, ← pow_two]
  unfold powerProfile
  by_cases small : |x| ≤ 1
  · rw [if_pos small]
    have square := log_square_power_bound |x| (-1 / 8) positive (by
      rw [abs_of_nonpos (Real.log_nonpos positive.le small)]
      ring)
    rw [show (-1 / 8 : ℝ) * 2 = -1 / 4 by norm_num] at square
    have bounded : ‖seedFourierRaw x‖ ≤ 1 := (seed_fourier_bound x).trans (by norm_num)
    calc
      _ ≤ (64 * |x| ^ (-1 / 4 : ℝ)) * 1 := mul_le_mul square bounded (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  · rw [if_neg small]
    have square := log_square_power_bound |x| (1 / 8) positive (by
      rw [abs_of_nonneg (Real.log_nonneg (le_of_not_ge small))]
      ring)
    rw [show (1 / 8 : ℝ) * 2 = 1 / 4 by norm_num] at square
    calc
      _ ≤ (64 * |x| ^ (1 / 4 : ℝ)) * |x|⁻¹ :=
        mul_le_mul square (seed_fourier_inverse_bound x nonzero) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add positive,
          show (1 / 4 : ℝ) + -1 = -3 / 4 by norm_num]

private theorem seed_second_fourier_memLp :
    MemLp (fun x : ℝ => (Real.log |x| : ℂ) * seedFourierLog x) 2 volume := by
  have envelope : MemLp powerEnvelopeRaw 2 volume := (Lp.memLp powerEnvelopeL2).ae_eq envelope_raw
  apply envelope.of_le_mul (c := 64)
    ((by fun_prop : Measurable (fun x : ℝ => (Real.log |x| : ℂ))).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable seedFourierLog))
  filter_upwards [seed_fourier_log_pair, seed_fourier_raw, volume.ae_ne (0 : ℝ)] with x logarithm raw nonzero
  change ‖(Real.log |x| : ℂ) * seedFourierLog x‖ ≤ 64 * ‖powerEnvelopeRaw x‖
  rw [logarithm, raw]
  exact (seed_square_log_bound x nonzero).trans
    (mul_le_mul_of_nonneg_left (envelope_norm x nonzero) (by norm_num))

private def seedSecondFourierLog : BurnolL2 := seed_second_fourier_memLp.toLp _

private theorem seed_second_fourier_log : LogPair seedFourierLog seedSecondFourierLog :=
  seed_second_fourier_memLp.coeFn_toLp

/-- The inverse Fourier logarithm of the original Gamma seed. -/
def actualGammaSeedFrequencyLog : BurnolL2 :=
  (Real.log q : ℂ) • seedFourierLog - inverseSynthesisLog + seedSecondFourierLog

theorem actual_gamma_seed_frequency_log :
    LogPair (fourierL2.symm actualGammaSeed) actualGammaSeedFrequencyLog := by
  have read : fourierL2.symm actualGammaSeed =
      ((Real.log q : ℂ) • fourierL2.symm C - fourierL2.symm (logSynthesis C)) +
        seedFourierLog := by
    rw [actualGammaSeed, log_seed_synthesis_apply, map_add, map_sub, map_smul,
      fourierL2.symm_apply_apply]
  rw [read]
  have head := logPair_smul (Real.log q : ℂ) _ _ seed_inverse_log
  have first := logPair_sub _ _ _ _ head inverse_synthesis_log
  exact log_pair_add _ _ _ _ first seed_second_fourier_log

end OriginalGamma.Source.KGamma.Iterated
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
