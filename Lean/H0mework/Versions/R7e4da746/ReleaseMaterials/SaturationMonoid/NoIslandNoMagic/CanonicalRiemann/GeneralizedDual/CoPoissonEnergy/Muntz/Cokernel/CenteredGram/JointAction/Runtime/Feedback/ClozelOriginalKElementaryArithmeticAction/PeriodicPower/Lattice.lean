import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.RiemannZeta

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Lattice
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszFinitePairing
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "b" => burnolRieszSingleFourierSource

def bSample (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolRadiusTruncatedFourierRaw q (b c:BurnolQuarterIntervalL2) x

def powerSample (c : BurnolCompletedMellinCoordinate) (n : ℕ) : ℂ :=
  (1/2:ℂ)*(n+1:ℂ)^(-star c.value)

theorem actual_original_lattice_value (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    burnolRieszStateRaw c (n+1)=powerSample c n-bSample c (n+1) := by
  rw [burnolRieszStateRaw_eq_positiveOuter c (by have := Nat.cast_nonneg (α:=ℝ) n;linarith)]
  unfold burnolRieszStatePositiveOuterRaw powerSample bSample
  rw [source_fourier_even]
  push_cast
  ring

private theorem positive_power_scale (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (x : ℝ) (positive : 0<x) :
    (Real.exp (h/2):ℂ)*((Real.exp h*x:ℝ):ℂ)^(-star c.value)=
      fullMellinTranslationCharacter (star c.value) h*(x:ℂ)^(-star c.value) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h).le positive.le]
  have exponential : (Real.exp h:ℂ)^(-star c.value)=Complex.exp ((h:ℂ)*(-star c.value)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)),
      ←Complex.ofReal_log (Real.exp_pos h).le,Real.log_exp]
  rw [exponential]
  change (Real.exp (h/2):ℂ)*(Complex.exp ((h:ℂ)*(-star c.value))*(x:ℂ)^(-star c.value))=_
  rw [←mul_assoc,Complex.ofReal_exp,←Complex.exp_add]
  unfold fullMellinTranslationCharacter
  push_cast
  congr 2
  ring

/-- The same canonical source is sampled after its actual half-density action. -/
theorem actual_original_shifted_lattice_value (c : BurnolCompletedMellinCoordinate)
    (h : ℝ) (lower : -Real.log 2≤h) (n : ℕ) :
    burnolRieszDilationRaw c h (n+1)=
      fullMellinTranslationCharacter (star c.value) h*powerSample c n-
        (Real.exp (h/2):ℂ)*bSample c (Real.exp h*(n+1)) := by
  have expLower : (1/2:ℝ)≤Real.exp h := by
    calc
      (1/2:ℝ)=Real.exp (-Real.log 2) := by
        rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num
      _≤Real.exp h := Real.exp_le_exp.mpr lower
  have positive : 0<(n+1:ℝ) := by positivity
  have outside : q<Real.exp h*(n+1) := by
    have nn := Nat.cast_nonneg (α:=ℝ) n
    nlinarith [Real.exp_pos h]
  rw [burnolRieszDilationRaw,burnolRieszStateRaw_eq_positiveOuter c outside]
  unfold burnolRieszStatePositiveOuterRaw bSample powerSample
  rw [source_fourier_even]
  have power := positive_power_scale c h (n+1) positive
  push_cast at power ⊢
  linear_combination (1/2:ℂ)*power

private theorem power_pair (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    star (powerSample c n)*powerSample c n=(1/4:ℂ)/(n+1:ℂ)^(c.value+star c.value) := by
  have positive : (0:ℝ)<n+1 := by positivity
  have ne : (n+1:ℂ)≠0 := by exact_mod_cast positive.ne'
  have asReal : ((n+1:ℝ):ℂ)=(n+1:ℂ) := by push_cast;rfl
  have angle : (n+1:ℂ).arg≠Real.pi := by
    rw [←asReal,Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_pos.ne
  have conjugate : star ((n+1:ℂ)^(-star c.value))=(n+1:ℂ)^(-c.value) := by
    have paid := (Complex.conj_cpow (n+1:ℂ) (-c.value) angle).symm
    simpa only [map_add,map_natCast,map_one,map_neg,star_def] using paid
  unfold powerSample
  rw [star_mul,show star (1/2:ℂ)=(1/2:ℂ) by norm_num,conjugate]
  calc
    _=(1/4:ℂ)*((n+1:ℂ)^(-c.value)*(n+1:ℂ)^(-star c.value)) := by ring
    _=(1/4:ℂ)*(n+1:ℂ)^(-(c.value+star c.value)) := by
      rw [←Complex.cpow_add _ _ ne]
      congr 2
      ring
    _=_ := by simp only [Complex.cpow_neg,div_eq_mul_inv]

/-- The full arithmetic power diagonal is paid by the convergent original zeta series at 2 Re(c). -/
theorem actual_power_lattice_price (c : BurnolCompletedMellinCoordinate) :
    HasSum (fun n:ℕ=>star (powerSample c n)*powerSample c n)
      ((1/4:ℂ)*riemannZeta (c.value+star c.value)) := by
  have right : 1<(c.value+star c.value).re := by
    simp only [add_re,star_def,conj_re]
    linarith [c.rightHalf]
  have series := (Complex.summable_one_div_nat_cpow.mpr right).comp_injective Nat.succ_injective
  have actual : Summable (fun n:ℕ=>1/(n+1:ℂ)^(c.value+star c.value)) := by
    simpa only [Function.comp_def,Nat.cast_succ] using series
  have sum : HasSum (fun n:ℕ=>1/(n+1:ℂ)^(c.value+star c.value))
      (riemannZeta (c.value+star c.value)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow right]
    exact actual.hasSum
  have formula : (fun n:ℕ=>star (powerSample c n)*powerSample c n)=
      (fun n:ℕ=>(1/4:ℂ)*(1/(n+1:ℂ)^(c.value+star c.value))) := by
    funext n
    rw [power_pair]
    ring
  rw [formula]
  exact sum.mul_left (1/4:ℂ)

end OriginalKElementaryArithmeticAction.PeriodicPower.Lattice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
