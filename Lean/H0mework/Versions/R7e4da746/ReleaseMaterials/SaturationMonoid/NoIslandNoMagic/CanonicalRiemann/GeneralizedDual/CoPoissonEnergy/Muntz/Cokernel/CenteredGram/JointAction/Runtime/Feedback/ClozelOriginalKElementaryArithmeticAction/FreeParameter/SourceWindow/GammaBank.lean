import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.FullPrice
import Mathlib.Analysis.Calculus.Deriv.ZPow

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalUnitMellinSource.Band
open scoped Topology BigOperators
local notation "L" => (Real.log 4:ℂ)
local notation "phase" s => fullMellinTranslationCharacter s (Real.log 16)

private theorem coordinate_not_one (c:BurnolCompletedMellinCoordinate) : 1-c.value≠0 := by
  intro zero
  have realPart:=congrArg Complex.re zero
  simp only [sub_re,one_re,zero_re] at realPart
  linarith [c.belowOne]

theorem actual_constant_coefficient_exp (s:ℂ) :
    constantCoefficient s=(1/2:ℂ)*(1-s)⁻¹*Complex.exp (L*s) := by
  unfold constantCoefficient
  rw [Complex.cpow_def_of_ne_zero (by norm_num:((1/4:ℝ):ℂ)≠0)]
  have logarithm:Complex.log ((1/4:ℝ):ℂ)= -L := by
    rw [←Complex.ofReal_log (by norm_num:(0:ℝ)≤1/4),
      show (1/4:ℝ)=(4:ℝ)⁻¹ by norm_num,Real.log_inv,Complex.ofReal_neg]
  rw [logarithm,neg_mul_neg]
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

private theorem pole_jet (j:Nat) (s:ℂ) :
    iteratedDeriv j (fun z:ℂ=>(1-z)⁻¹) s=(j.factorial:ℂ)/(1-s)^(j+1) := by
  have linear:=congrArg (fun f:ℂ→ℂ=>f s) (iter_deriv_inv_linear j (-1:ℂ) 1)
  rw [←iteratedDeriv_eq_iterate] at linear
  have same:(fun z:ℂ=>((-1:ℂ)*z+1)⁻¹)=(fun z:ℂ=>(1-z)⁻¹):=by
    ext z
    congr 1
    ring
  rw [same] at linear
  have signs:(-1:ℂ)^j*(-1:ℂ)^j=1:=by rw [←mul_pow];simp
  have exponent:(-1-(j:ℤ))= -(j+1:Nat):=by omega
  rw [exponent,zpow_neg,zpow_natCast] at linear
  calc
    _=((-1:ℂ)^j*(-1:ℂ)^j)*(j.factorial:ℂ)*((1-s)^(j+1))⁻¹ := by
      rw [linear]
      congr 1 <;> ring
    _=_ := by rw [signs];ring

/-- The original constant coefficient has this complete derivative bank, including every lower clock. -/
theorem actual_constant_coefficient_jet (c:BurnolCompletedMellinCoordinate) (m:Nat) :
    iteratedDeriv m constantCoefficient c.value=
      ∑ j∈Finset.range (m+1),(m.choose j:ℂ)*L^(m-j)*constantCoefficient c.value*
        (j.factorial:ℂ)/(1-c.value)^j := by
  have represented:constantCoefficient=(fun s:ℂ=>(1/2:ℂ)*((1-s)⁻¹*Complex.exp (L*s))):=by
    ext s
    rw [actual_constant_coefficient_exp]
    ring
  conv_lhs=>rw [represented,iteratedDeriv_const_mul_field]
  have pole:ContDiffAt ℂ m (fun s:ℂ=>(1-s)⁻¹) c.value:=
    (contDiffAt_const.sub contDiffAt_id).inv (coordinate_not_one c)
  have exponential:ContDiffAt ℂ m (fun s:ℂ=>Complex.exp (L*s)) c.value:=by fun_prop
  have product:=iteratedDeriv_fun_mul pole exponential
  rw [product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j member
  rw [pole_jet,iteratedDeriv_cexp_const_mul,actual_constant_coefficient_exp,pow_succ]
  field_simp [coordinate_not_one c]

theorem actual_phase_mean_zero (c:BurnolCompletedMellinCoordinate) :
    (1/2:ℂ)*(phase c.value)⁻¹*bandMean c 0= -constantCoefficient c.value := by
  rw [actual_constant_coefficient_exp]
  unfold bandMean fullMellinTranslationCharacter
  rw [Complex.cpow_def_of_ne_zero (by norm_num:(4:ℂ)≠0),
    show Complex.log (4:ℂ)=L from (Complex.ofReal_log (by norm_num:(0:ℝ)≤4)).symm,
    ←Complex.exp_neg]
  have logarithm:Real.log 16=2*Real.log 4:=by
    rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow]
    norm_num
  rw [logarithm]
  simp only [pow_zero,one_mul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have combined:Complex.exp (-((1/2-c.value)*(2*L)))*Complex.exp (L*(1-c.value))=
      Complex.exp (L*c.value) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  calc
    _= (-(1/2:ℂ)/(1-c.value))*(Complex.exp (-((1/2-c.value)*(2*L)))*
      Complex.exp (L*(1-c.value))) := by ring
    _=_ := by rw [combined];ring

private theorem actual_phase_mean_term (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    (1/2:ℂ)*(phase c.value)⁻¹*((j.factorial:ℂ)/(2:ℂ)^j)*bandMean c j=
      -constantCoefficient c.value*(j.factorial:ℂ)/(1-c.value)^j := by
  have source:=actual_phase_mean_zero c
  have gamma:bandMean c j=(2/(1-c.value))^j*bandMean c 0 := by
    simp only [bandMean,pow_zero,one_mul]
  rw [gamma,div_pow]
  have ne:(2:ℂ)^j≠0:=pow_ne_zero _ (by norm_num)
  have paid:=congrArg (fun z:ℂ=>z*(j.factorial:ℂ)/(1-c.value)^j) source
  field_simp [ne] at paid ⊢
  linear_combination paid

def gammaBank (c:BurnolCompletedMellinCoordinate) (m:Nat) : ℂ :=
  (1/2:ℂ)*(phase c.value)⁻¹*
    ∑ j∈Finset.range (m+1),(m.choose j:ℂ)*L^(m-j)*((j.factorial:ℂ)/(2:ℂ)^j)*bandMean c j

/-- The entire Unit mean bank cancels the original constant coefficient jet on the same full mass. -/
theorem actual_gamma_bank_cancellation (c:BurnolCompletedMellinCoordinate) (m:Nat) :
    gammaBank c m+iteratedDeriv m constantCoefficient c.value=0 := by
  rw [gammaBank,actual_constant_coefficient_jet,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j member
  have source:=actual_phase_mean_term c j
  have paid:=congrArg (fun z:ℂ=>(m.choose j:ℂ)*L^(m-j)*z) source
  linear_combination paid

/-- All lower logarithmic coefficients are consumed by the same binomial clock, rather than discarded. -/
theorem actual_log_bank (m:Nat) (z:ℂ) :
    (∑ j∈Finset.range (m+1),(m.choose j:ℂ)*L^(m-j)*((j.factorial:ℂ)/(2:ℂ)^j)*
      bandCoefficient j*z^j)=(L+z)^m := by
  calc
    _=∑ j∈Finset.range (m+1),(m.choose j:ℂ)*L^(m-j)*z^j := by
      apply Finset.sum_congr rfl
      intro j member
      unfold bandCoefficient
      have factorial:(j.factorial:ℂ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have power:(2:ℂ)^j≠0:=pow_ne_zero _ (by norm_num)
      field_simp [factorial,power]
    _=(z+L)^m := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j member
      ring
    _=_ := by rw [add_comm]

/-- The actual first-cell logarithm and the radius clock combine to log(16 |x|). -/
theorem actual_log_bank_profile (m:Nat) (x:ℝ) (nonzero:x≠0) :
    (∑ j∈Finset.range (m+1),(m.choose j:ℂ)*L^(m-j)*((j.factorial:ℂ)/(2:ℂ)^j)*
      bandCoefficient j*(bandLog |x|)^j)=((Real.log (16*|x|):ℝ):ℂ)^m := by
  rw [actual_log_bank]
  congr 1
  unfold bandLog
  rw [Real.log_mul (by norm_num:(16:ℝ)≠0) (abs_ne_zero.mpr nonzero)]
  have quarter:Real.log (1/4:ℝ)= -Real.log 4 := by
    rw [show (1/4:ℝ)=(4:ℝ)⁻¹ by norm_num,Real.log_inv]
  have sixteen:Real.log 16=2*Real.log 4:=by
    rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow]
    norm_num
  rw [quarter,sixteen]
  push_cast
  ring

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
