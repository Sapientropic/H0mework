import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Arithmetic
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Seed
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Arithmetic OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
open scoped Topology InnerProductSpace
open private position_exterior_read fourier_exterior_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Source
open private even_eq_of_positive from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate
open private jointInput_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
open private lower_threshold reciprocal_threshold from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Arithmetic
local notation "q" => (1/4 : ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "D" => burnolMultiplicativeDilation
local notation "A" => sourceAnnulusCut

private theorem position_seed_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    (positionSeed c h : ℝ → ℂ) =ᵐ[volume] bandRaw h (positionSource c) := by
  rw [positionSeed_eq_exterior c h nonnegative]
  exact position_exterior_read c h nonnegative

private theorem fourier_seed_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    (fourierSeed c h : ℝ → ℂ) =ᵐ[volume] bandRaw h (burnolRieszSingleFourierSourceRaw c) := by
  rw [fourierSeed_eq_exterior c h nonnegative]
  exact fourier_exterior_read c h nonnegative

private theorem seed_even (field : BurnolL2) (h : ℝ) (raw : ℝ → ℂ)
    (represents : (field : ℝ → ℂ) =ᵐ[volume] bandRaw h raw) : reflectL2 field = field :=
  burnolReflectL2_eq_of_even_raw _ _ represents (fun x => by simp only [bandRaw, abs_neg])

private theorem tate_seed_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    (T (positionSeed c h) : ℝ → ℂ) =ᵐ[volume] burnolTateReciprocalRaw (bandRaw h (positionSource c)) := by
  have read := position_seed_raw c h nonnegative
  exact (burnolTateReciprocalL2_coeFn _).trans
    (burnolTateReciprocalRaw_ae_congr (Lp.memLp _) ((Lp.memLp _).ae_eq read) read)

private theorem seed_upper_threshold (h x : ℝ) (positive : 0 < x) :
    x⁻¹ ≤ q * Real.exp h ↔ 4 * Real.exp (-h) ≤ x := by
  have inverse : (Real.exp h*x)⁻¹ = Real.exp (-h)*x⁻¹ := by
    rw [mul_inv_rev, Real.exp_neg, mul_comm]
  rw [← lower_threshold h x⁻¹, ← inverse]
  exact reciprocal_threshold h x positive

/-- The full moving K-counted field is the same occurrence as the original two CoPoisson seeds. -/
theorem actual_joint_input_original_seeds (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    jointInput c zero h = (1/2 : ℂ) • (T (positionSeed c h) + fourierSeed c h) := by
  have pEven := seed_even _ h _ (position_seed_raw c h nonnegative)
  have fEven := seed_even _ h _ (fourier_seed_raw c h nonnegative)
  have rightEven : reflectL2 ((1/2 : ℂ) • (T (positionSeed c h) + fourierSeed c h)) =
      (1/2 : ℂ) • (T (positionSeed c h) + fourierSeed c h) := by
    rw [map_smul, map_add, ← burnolTateReciprocal_reflect, pEven, fEven]
  apply even_eq_of_positive _ _ (jointInput_even c zero h) rightEven
  have plusUpper : Real.exp h ≤ 2 := by
    have exponential := Real.exp_le_exp.mpr bounded
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at exponential
  filter_upwards [actual_joint_input_arithmetic_raw c zero h nonnegative bounded,
    sourceAnnulusCut_coeFn (pairedBurnolMultiplicativeDilation h (countedKernel c zero)),
    tate_seed_raw c h nonnegative, fourier_seed_raw c h nonnegative,
    Lp.coeFn_smul (1/2 : ℂ) (T (positionSeed c h) + fourierSeed c h),
    Lp.coeFn_add (T (positionSeed c h)) (fourierSeed c h), volume.ae_ne (4 : ℝ)]
    with x original cut position fourier scalar addition notFour positive
  rw [scalar, Pi.smul_apply, smul_eq_mul, addition, Pi.add_apply, position, fourier]
  unfold burnolTateReciprocalRaw
  rw [abs_of_pos positive, bandRaw, abs_inv, abs_of_pos positive]
  by_cases band : q < x ∧ x < 4
  · rw [original band]
    have reciprocal : q < x⁻¹ := by
      rw [← one_div, lt_div_iff₀ positive]
      nlinarith [band.2]
    simp only [reciprocal, true_and, seed_upper_threshold h x positive, bandRaw,
      abs_of_pos positive, band.1]
    have inverse : Real.exp (-h)*x⁻¹ = (Real.exp h*x)⁻¹ := by
      rw [Real.exp_neg, mul_inv_rev, mul_comm]
    rw [inverse]
    by_cases lower : x ≤ q * Real.exp h <;>
      by_cases upper : 4 * Real.exp (-h) ≤ x <;>
        simp only [lower, upper, ↓reduceIte] <;> ring
  · have cutZero : jointInput c zero h x = 0 := by
      change A (pairedBurnolMultiplicativeDilation h (countedKernel c zero)) x = 0
      rw [cut, abs_of_pos positive, if_neg]
      intro inside
      exact band ⟨inside.1, lt_of_le_of_ne inside.2 notFour⟩
    rw [cutZero]
    have first : ¬ (q < x⁻¹ ∧ x⁻¹ ≤ q * Real.exp h) := by
      intro active
      have lower : q < x := by
        have scaled : 1 ≤ (q * Real.exp h) * x :=
          (div_le_iff₀ positive).mp (show 1/x ≤ q*Real.exp h by simpa only [one_div] using active.2)
        nlinarith
      have upper : x < 4 := by
        have bound : q < 1/x := by simpa only [one_div] using active.1
        rw [lt_div_iff₀ positive] at bound
        nlinarith only [bound]
      exact band ⟨lower, upper⟩
    have second : ¬ (q < x ∧ x ≤ q * Real.exp h) := by
      intro active
      exact band ⟨active.1, lt_of_le_of_lt active.2 (by nlinarith : q * Real.exp h < 4)⟩
    rw [if_neg first, bandRaw, abs_of_pos positive, if_neg second, mul_zero, add_zero, mul_zero]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Seed
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
