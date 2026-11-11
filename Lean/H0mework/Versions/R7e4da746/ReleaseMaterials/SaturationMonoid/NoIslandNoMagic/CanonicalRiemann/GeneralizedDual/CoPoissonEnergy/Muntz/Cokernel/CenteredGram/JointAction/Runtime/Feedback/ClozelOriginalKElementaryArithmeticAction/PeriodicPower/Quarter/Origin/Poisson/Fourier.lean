import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Fourier
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source
open scoped Topology FourierTransform

theorem actual_alias_origin (c:BurnolCompletedMellinCoordinate):
    (∑'k:ℤ,scaledAliasTerm c 1 k)=aliasRaw c 0:=by
  apply tsum_congr
  intro k
  simp only [scaledAliasTerm,aliasRawTerm,one_mul,zero_add]

theorem actual_fourier_lattice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h):
    (∑'k:ℤ,𝓕 (compactRaw c h) (k:ℝ))=
      -jumpCoefficient c/2*((Real.exp (h/2):ℂ)-waveCharacter c h)+
      (Real.exp (h/2):ℂ)*(∑'k:ℤ,scaledAliasTerm c (Real.exp h) k)-
      waveCharacter c h*aliasRaw c 0:=by
  have bank:HasSum (fun k:ℤ=>(if k=0 then 𝓕 (compactRaw c h) 0 else 0)+
      (Real.exp (h/2):ℂ)*scaledAliasTerm c (Real.exp h) k-waveCharacter c h*scaledAliasTerm c 1 k)
      (𝓕 (compactRaw c h) 0+(Real.exp (h/2):ℂ)*(∑'k:ℤ,scaledAliasTerm c (Real.exp h) k)-
        waveCharacter c h*(∑'k:ℤ,scaledAliasTerm c 1 k)):=
    ((hasSum_ite_eq 0 _).add
      ((actual_scaled_alias_summable c (Real.exp h) (Real.exp_pos h)).hasSum.mul_left _)).sub
      ((actual_scaled_alias_summable c 1 (by norm_num)).hasSum.mul_left _)
  have source:HasSum (fun k:ℤ=>𝓕 (compactRaw c h) (k:ℝ))
      (𝓕 (compactRaw c h) 0+(Real.exp (h/2):ℂ)*(∑'k:ℤ,scaledAliasTerm c (Real.exp h) k)-
        waveCharacter c h*(∑'k:ℤ,scaledAliasTerm c 1 k)):=by
    apply bank.congr_fun
    intro k
    by_cases zero:k=0
    · subst k;simp [scaledAliasTerm]
    · simp only [if_neg zero,zero_add,scaledAliasTerm,one_mul]
      exact actual_fourier_difference c h nn (k:ℝ) (by exact_mod_cast zero)
  simpa only [actual_compact_fourier_zero c h nn,actual_alias_origin] using source.tsum_eq

def inverseSquareMass:ℝ:=∑'k:ℤ,1/(k:ℝ)^2

theorem actual_inverse_square_nonnegative:0 ≤ inverseSquareMass:=
  tsum_nonneg (fun k=>by positivity)

theorem actual_scaled_alias_sum_bound (c:BurnolCompletedMellinCoordinate) (r:ℝ) (positive:0<r):
    ‖∑'k:ℤ,scaledAliasTerm c r k‖≤tailBound c/r^2*inverseSquareMass:=by
  have major:Summable (fun k:ℤ=>(tailBound c/r^2)/(k:ℝ)^2):=by
    apply ((Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (tailBound c/r^2)).congr
    intro k
    ring
  have normsum:Summable (fun k:ℤ=>‖scaledAliasTerm c r k‖):=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (actual_scaled_alias_bound c r positive) major
  calc
    _≤∑'k:ℤ,‖scaledAliasTerm c r k‖:=norm_tsum_le_tsum_norm normsum
    _≤∑'k:ℤ,(tailBound c/r^2)/(k:ℝ)^2:=
      normsum.tsum_le_tsum (actual_scaled_alias_bound c r positive) major
    _=tailBound c/r^2*inverseSquareMass:=by
      unfold inverseSquareMass
      rw [←tsum_mul_left]
      apply tsum_congr
      intro k
      ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Fourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
