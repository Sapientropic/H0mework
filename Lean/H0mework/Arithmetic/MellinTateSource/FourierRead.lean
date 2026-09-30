import H0mework.Arithmetic.MellinTateSource.FourierPairing
import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusFourierLanding
import H0mework.Arithmetic.MobiusSource.MobiusFiniteCutoff

/-! # Actual Fourier read and finite Möbius recovery for compact sources -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set Filter
open scoped SchwartzMap ContDiff

noncomputable section

/-- The ordinary Fourier-side co-Poisson function. Its constant is the
second source mean, not a caller-selected representative. -/
def burnolCompactFourierCoSum
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  (∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ *
      source.1 (t / (n + 1 : ℕ))) +
    burnolCompactAdditiveFourierGapConstant source

theorem burnolCompactFourierCoSum_eq_reciprocalCoSum
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCompactFourierCoSum source t =
      burnolCompactAdditiveCoSum (burnolCompactTateReciprocalSource source) t := by
  rw [burnolCompactFourierCoSum, burnolCompactAdditiveCoSum,
    burnolCompactTateReciprocalSource_normalization]
  simp_rw [burnolCompactTateReciprocalSource_additiveSource]
  ring

/-- The Fourier `L²` generator is exactly the additive co-sum of the actual
Tate reciprocal source. -/
theorem burnolCompactFourierL2_eq_reciprocalL2
    (source : burnolCompactAnnulusSource) :
    fourierL2 (burnolCompactAdditiveL2 source) =
      burnolCompactAdditiveL2 (burnolCompactTateReciprocalSource source) := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (fourierL2
      (burnolCompactAdditiveL2 source))).locallyIntegrable (by norm_num)
  · exact (Lp.memLp (burnolCompactAdditiveL2
      (burnolCompactTateReciprocalSource source))).locallyIntegrable (by norm_num)
  · intro realTest testSmooth testCompact
    have compactComplex : HasCompactSupport (Complex.ofRealCLM ∘ realTest) :=
      testCompact.comp_left rfl
    let test : SchwartzMap ℝ ℂ := compactComplex.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp testSmooth)
    calc
      (∫ x : ℝ, realTest x •
          (fourierL2 (burnolCompactAdditiveL2 source) : ℝ → ℂ) x) =
          ((fourierL2 (burnolCompactAdditiveL2 source) : BurnolL2) :
            TemperedDistribution ℝ ℂ) test := by
        simp [test, Function.comp_apply, real_smul]
      _ = ∫ x : ℝ, FourierTransform.fourier test x *
          burnolCompactAdditiveCoSum source x :=
        burnolCompactAdditiveFourierL2_toTemperedDistribution_apply source test
      _ = ∫ x : ℝ, test x * burnolCompactAdditiveCoSum
          (burnolCompactTateReciprocalSource source) x :=
        burnolCompactFourier_pairing source test
      _ = ∫ x : ℝ, realTest x •
          (burnolCompactAdditiveL2
            (burnolCompactTateReciprocalSource source) : ℝ → ℂ) x := by
        apply integral_congr_ae
        filter_upwards [burnolCompactAdditiveL2_coeFn
          (burnolCompactTateReciprocalSource source)] with x hx
        rw [hx]
        rfl

/-- The explicit reciprocal co-sum is an actual Fourier representative. -/
theorem burnolCompactFourierL2_ae_eq_coSum
    (source : burnolCompactAnnulusSource) :
    (fourierL2 (burnolCompactAdditiveL2 source) : ℝ → ℂ) =ᵐ[volume]
      burnolCompactFourierCoSum source := by
  filter_upwards [burnolCompactAdditiveL2_coeFn
      (burnolCompactTateReciprocalSource source)] with t ht
  rw [burnolCompactFourierL2_eq_reciprocalL2 source, ht,
    ← burnolCompactFourierCoSum_eq_reciprocalCoSum source t]

theorem burnolCompactFourierCoSum_quarterGap
    (source : burnolCompactAnnulusSource) {t : ℝ}
    (inside : |t| ≤ (1 / 4 : ℝ)) :
    burnolCompactFourierCoSum source t =
      burnolCompactFourierCoSum source 0 := by
  rw [burnolCompactFourierCoSum_eq_reciprocalCoSum,
    burnolCompactFourierCoSum_eq_reciprocalCoSum,
    burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
      (burnolCompactTateReciprocalSource source) inside,
    burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
      (burnolCompactTateReciprocalSource source) (by norm_num)]

/-- Existing centred Möbius inversion recovers the uninverted compact source. -/
theorem burnolCompactFourierCoSum_mobius_recovers_source
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCenteredMobiusInverse (burnolCompactFourierCoSum source) t =
      source.1 t := by
  rw [funext (burnolCompactFourierCoSum_eq_reciprocalCoSum source),
    burnolCompactCenteredMobiusInverse_roundtrip,
    burnolCompactTateReciprocalSource_additiveSource]

/-- On the fixed annulus recovery is the finite sum with cutoff `m < 16`. -/
theorem burnolCompactFourierCoSum_fixedAnnulusFinite_recovers_source
    (source : burnolCompactAnnulusSource) {t : ℝ}
    (annulus : (1 / 4 : ℝ) ≤ |t| ∧ |t| ≤ 4) :
    (∑ m ∈ burnolCenteredMobiusCutoffFinset (4 : ℝ),
        burnolCenteredMobiusSummand (burnolCompactFourierCoSum source) t m) =
      source.1 t := by
  rw [← burnolCompactFourierCoSum_mobius_recovers_source source t]
  change (∑ m ∈ burnolCenteredMobiusCutoffFinset (4 : ℝ),
      burnolCenteredMobiusSummand (burnolCompactFourierCoSum source) t m) =
    ∑' m : ℕ+,
      burnolCenteredMobiusSummand (burnolCompactFourierCoSum source) t m
  symm
  rw [tsum_eq_sum (s := burnolCenteredMobiusCutoffFinset (4 : ℝ))]
  intro m outside
  apply burnolCenteredMobiusSummand_eq_zero_of_cutoff_le
    (burnolCompactFourierCoSum source)
    (fun {_} inside ↦ burnolCompactFourierCoSum_quarterGap source inside)
  have cutoffLe : burnolCenteredMobiusCutoff t ≤
      burnolCenteredMobiusCutoff (4 : ℝ) := by
    unfold burnolCenteredMobiusCutoff
    apply Nat.ceil_mono
    simpa using mul_le_mul_of_nonneg_left annulus.2 (by norm_num : (0 : ℝ) ≤ 4)
  exact cutoffLe.trans (Nat.le_of_not_gt (by simpa using outside))

/-- Reciprocal recharting of the same extraction recovers the original
inverted additive source. -/
theorem burnolCompactFourierCoSum_mobius_recovers_reciprocal
    (source : burnolCompactAnnulusSource) (u : ℝ) :
    (((|u| : ℝ) : ℂ)⁻¹) *
        burnolCenteredMobiusInverse (burnolCompactFourierCoSum source) u⁻¹ =
      burnolCompactAdditiveSource source u := by
  rw [burnolCompactFourierCoSum_mobius_recovers_source]
  by_cases hu : u = 0
  · subst u
    simp [burnolCompactAdditiveSource]
  · rw [burnolCompactAdditiveSource, if_neg hu]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
