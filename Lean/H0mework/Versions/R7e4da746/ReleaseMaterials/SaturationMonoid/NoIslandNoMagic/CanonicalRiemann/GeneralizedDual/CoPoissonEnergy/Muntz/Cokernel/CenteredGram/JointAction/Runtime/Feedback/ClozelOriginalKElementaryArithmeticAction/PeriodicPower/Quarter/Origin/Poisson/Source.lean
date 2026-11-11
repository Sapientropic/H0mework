import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
open scoped Topology FourierTransform

def scaledAliasTerm (c:BurnolCompletedMellinCoordinate) (r:ℝ) (k:ℤ):ℂ :=
  if k=0 then 0 else resolvedFourierRaw c (r*(k:ℝ))

theorem actual_scaled_alias_bound (c:BurnolCompletedMellinCoordinate) (r:ℝ) (positive:0<r)
    (k:ℤ):‖scaledAliasTerm c r k‖≤(tailBound c/r^2)/(k:ℝ)^2 := by
  by_cases zero:k=0
  · simp [scaledAliasTerm,zero]
  · rw [scaledAliasTerm,if_neg zero]
    have nonzero:(k:ℝ)≠0:=by exact_mod_cast zero
    calc
      _≤tailBound c/|r*(k:ℝ)|^2:=actual_resolved_fourier_bound c _ (mul_ne_zero positive.ne' nonzero)
      _=(tailBound c/r^2)/(k:ℝ)^2:=by rw [sq_abs,mul_pow];ring

theorem actual_scaled_alias_summable (c:BurnolCompletedMellinCoordinate) (r:ℝ) (positive:0<r):
    Summable (scaledAliasTerm c r) := by
  have major:Summable (fun k:ℤ=>(tailBound c/r^2)/(k:ℝ)^2):=by
    apply ((Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (tailBound c/r^2)).congr
    intro k
    ring
  exact Summable.of_norm_bounded major (actual_scaled_alias_bound c r positive)

theorem actual_compact_fourier_summable (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    Summable (fun k:ℤ=>𝓕 (compactRaw c h) (k:ℝ)) := by
  have zero:Summable (fun k:ℤ=>if k=0 then 𝓕 (compactRaw c h) 0 else 0):=(hasSum_ite_eq 0 _).summable
  have moved:Summable (fun k:ℤ=>(Real.exp (h/2):ℂ)*scaledAliasTerm c (Real.exp h) k):=
    (actual_scaled_alias_summable c (Real.exp h) (Real.exp_pos h)).mul_left _
  have direct:Summable (fun k:ℤ=>waveCharacter c h*scaledAliasTerm c 1 k):=
    (actual_scaled_alias_summable c 1 (by norm_num)).mul_left _
  apply (zero.add (moved.sub direct)).congr
  intro k
  by_cases atzero:k=0
  · subst k;simp [scaledAliasTerm]
  · simp only [if_neg atzero,zero_add,scaledAliasTerm,one_mul]
    exact (actual_fourier_difference c h nonnegative (k:ℝ) (by exact_mod_cast atzero)).symm

theorem actual_poisson (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    ∑'n:ℤ,compactRaw c h (n:ℝ)=∑'k:ℤ,𝓕 (compactRaw c h) (k:ℝ) := by
  have source:=Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (actual_compact_raw_continuous c h) (b:=2) (by norm_num)
    (actual_compact_decay c h nonnegative)
  simpa only [zero_add,AddCircle.coe_zero,fourier_eval_zero,mul_one] using
    source (actual_compact_fourier_summable c h nonnegative) 0

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
