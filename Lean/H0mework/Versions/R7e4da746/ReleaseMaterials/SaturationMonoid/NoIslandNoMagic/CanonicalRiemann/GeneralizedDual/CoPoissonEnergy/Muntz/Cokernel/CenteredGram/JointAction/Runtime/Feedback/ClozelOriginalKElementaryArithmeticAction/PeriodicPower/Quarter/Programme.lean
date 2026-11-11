import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Finite
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Programme
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Lattice OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Programme
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Finite
open scoped Topology BigOperators InnerProductSpace
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local notation "q" => ((1/4:ℝ):AddCircle (1:ℝ))
open private powerCoefficient_nat from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Finite

/-- The original integer enumeration differs from the symmetric programme by its actual last half-mode. -/
theorem actual_programme_symmetry (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
 finiteMap c N=symmetricMap c N+powerCoefficient c (-(N:ℤ)) • _root_.fourier (-(N:ℤ)) := by
 induction N with
 | zero => simp [finiteMap,symmetricMap,powerCoefficient_zero]
 | succ N ih =>
  cases N with
  | zero =>
   simp only [finiteMap,symmetricMap,Finset.range_one,Finset.sum_singleton,Finset.Ico_self,
    Finset.sum_empty,Nat.cast_zero,Nat.cast_one,powerCoefficient_zero,zero_smul,zero_add]
  | succ N =>
   have positive:(1:ℕ)≤N+1:=by omega
   rw [finiteMap,Finset.sum_range_succ]
   change finiteMap c (N+1)+_=_
   rw [ih]
   have symm:symmetricMap c (N+1+1)=symmetricMap c (N+1)+
     powerCoefficient c (N+1) • (_root_.fourier ((N+1:ℕ):ℤ)+_root_.fourier (-((N+1:ℕ):ℤ))):=by
    rw [symmetricMap,Finset.sum_Ico_succ_top positive]
    rfl
   rw [symm,show powerCoefficient c (-((N+1:ℕ):ℤ))=powerCoefficient c (N+1) from powerCoefficient_even c _,smul_add]
   push_cast
   module

theorem actual_quarter_half_mode (c:BurnolCompletedMellinCoordinate) (M:ℕ) :
 finiteMap c (4*(M+1)) q=symmetricMap c (4*(M+1)) q+powerCoefficient c (4*(M+1)) := by
 rw [actual_programme_symmetry]
 simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
 have phase:_root_.fourier (-((4*(M+1):ℕ):ℤ)) q=1:=by
  rw [_root_.fourier_neg,_root_.fourier_coe_apply]
  have expSource:Complex.exp (2*Real.pi*Complex.I*((4*(M+1):ℕ):ℤ)*(1/4:ℝ)/1)=1:=by
   convert Complex.exp_nat_mul_two_pi_mul_I (M+1) using 1
   congr 1
   push_cast
   ring
  norm_num only [Complex.ofReal_one]
  rw [expSource]
  simp
 rw [phase,mul_one,powerCoefficient_even]
 push_cast
 rfl

private theorem half_mode_zero (c:BurnolCompletedMellinCoordinate) :
 Tendsto (fun M:ℕ=>powerCoefficient c (4*(M+1))) atTop (𝓝 0) := by
 have index:Tendsto (fun M:ℕ=>(4*(M+1):ℕ)) atTop atTop:=
  ((strictMono_mul_left_of_pos (by decide:(0:ℕ)<4)).comp
    (strictMono_nat_of_lt_succ (by intro n;omega))).tendsto_atTop
 have realIndex:Tendsto (fun M:ℕ=>((4*(M+1):ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp index
 have realPrice: Tendsto (fun M:ℕ=>((4*(M+1):ℕ):ℝ)^(-c.value.re)) atTop (𝓝 0):=
  (tendsto_rpow_neg_atTop (by linarith [c.rightHalf]:0<c.value.re)).comp realIndex
 rw [tendsto_zero_iff_norm_tendsto_zero]
 have paid:=realPrice.const_mul (1/2:ℝ)
 simp only [mul_zero] at paid
 apply paid.congr'
 filter_upwards with M
 have coefficient:=powerCoefficient_nat c (4*(M+1)) (by omega)
 push_cast at coefficient
 rw [coefficient,norm_mul]
 have raw:(4:ℂ)*(M+1)=(((4*(M+1):ℕ):ℝ):ℂ):=by push_cast;rfl
 rw [raw,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
 simp only [neg_re,star_def,conj_re]
 norm_num

/-- The literal V79 finite programme has the new original-zero quarter read, with its last mode paid. -/
theorem actual_original_programme_zero_quarter (c:BurnolCompletedMellinCoordinate)
 (zero:riemannZeta c.value=0) :
 Tendsto (fun M:ℕ=>finiteMap c (4*(M+1)) q) atTop (𝓝 0) := by
 have source:=(actual_original_zero_quarter c zero).add (half_mode_zero c)
 simp only [add_zero] at source
 apply source.congr'
 filter_upwards with M
 exact (actual_quarter_half_mode c M).symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Programme
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
