import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineSource
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalGrouping
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineSource
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open scoped BigOperators

abbrev AngularExponent := Fin 3 →₀ ℕ
abbrev AngularPolynomial := MvPolynomial (Fin 3) Symbol

def scalarJordan (r : ℕ) (f g : Symbol) : Symbol := fun zp => (jordan r f g zp).re

theorem scalarJordan_native (r : ℕ) (f g : Symbol) (zp : Phase) :
    (scalarJordan r f g zp : ℂ)=jordan r f g zp := by
  have hermitian : star (jordan r f g zp)=jordan r f g zp := by
    have left := coefficient_adjoint_swap r f g zp
    have right := coefficient_adjoint_swap r g f zp
    change starRingEnd ℂ (coefficient r f g zp)=coefficient r g f zp at left
    change starRingEnd ℂ (coefficient r g f zp)=coefficient r f g zp at right
    simp only [jordan,Complex.star_def,map_div₀,map_add,map_ofNat,left,right]
    norm_num
    ring
  have imag : (jordan r f g zp).im=0 := Complex.conj_eq_iff_im.mp hermitian
  apply Complex.ext
  · rfl
  · exact imag.symm

theorem scalarJordan_zero (f g : Symbol) : scalarJordan 0 f g=f*g := by
  funext zp
  simp [scalarJordan,jordan,coefficient_zero]
  ring

theorem scalarJordan_odd (r : ℕ) (f g : Symbol) : scalarJordan (2*r+1) f g=0 := by
  funext zp
  simp only [scalarJordan,jordan_odd,Complex.zero_re,Pi.zero_apply]

theorem scalarJordan_zero_left (r : ℕ) (g : Symbol) : scalarJordan r 0 g=0 := by
  funext zp
  change ((coefficient r (fun _ => 0) g zp+coefficient r g (fun _ => 0) zp)/2).re=0
  rw [coefficient_zero_left,coefficient_zero_right]
  norm_num

theorem scalarJordan_zero_right (r : ℕ) (f : Symbol) : scalarJordan r f 0=0 := by
  funext zp
  change ((coefficient r f (fun _ => 0) zp+coefficient r (fun _ => 0) f zp)/2).re=0
  rw [coefficient_zero_left,coefficient_zero_right]
  norm_num

def weighted (r : ℕ) (P Q : AngularPolynomial) : AngularPolynomial :=
  ∑ u ∈ P.support,∑ v ∈ Q.support,
    MvPolynomial.monomial (u+v) (scalarJordan r (MvPolynomial.coeff u P) (MvPolynomial.coeff v Q))

theorem weighted_monomial (r : ℕ) (u v : AngularExponent) (f g : Symbol) :
    weighted r (MvPolynomial.monomial u f) (MvPolynomial.monomial v g)=
      MvPolynomial.monomial (u+v) (scalarJordan r f g) := by
  classical
  by_cases hf : f=0
  · subst f
    simp [weighted,scalarJordan_zero_left]
  · by_cases hg : g=0
    · subst g
      simp [weighted,scalarJordan_zero_right]
    · simp [weighted,MvPolynomial.support_monomial,hf,hg]

theorem weighted_constants (r : ℕ) (f g : Symbol) :
    weighted r (MvPolynomial.C f) (MvPolynomial.C g)=MvPolynomial.C (scalarJordan r f g) := by
  simpa only [MvPolynomial.monomial_zero',zero_add] using weighted_monomial r 0 0 f g

theorem weighted_zero (P Q : AngularPolynomial) : weighted 0 P Q=P*Q := by
  unfold weighted
  simp only [scalarJordan_zero]
  conv_rhs => rw [MvPolynomial.as_sum P,MvPolynomial.as_sum Q]
  simp only [Finset.sum_mul,Finset.mul_sum,MvPolynomial.monomial_mul]
  exact Finset.sum_comm

def angularMoment (u : AngularExponent) : ℝ :=
  if ∀ j : Fin 3,Even (u j) then
    (∏ j : Fin 3,((u j-1).doubleFactorial : ℝ))/
      (((∑ j : Fin 3,u j)+1).doubleFactorial : ℝ)/((∑ j : Fin 3,u j)+2)
  else 0

def average (P : AngularPolynomial) : Symbol :=
  ∑ u ∈ P.support,fun zp => angularMoment u*(MvPolynomial.coeff u P) zp

theorem angularMoment_zero : angularMoment 0=1/2 := by
  norm_num [angularMoment,Nat.doubleFactorial]

theorem angularMoment_odd (u : AngularExponent) (j : Fin 3) (odd : Odd (u j)) : angularMoment u=0 := by
  have fails : ¬ ∀ i : Fin 3,Even (u i) := fun h => (Nat.not_even_iff_odd.mpr odd) (h j)
  simp only [angularMoment,fails,if_false]

theorem average_monomial (u : AngularExponent) (f : Symbol) :
    average (MvPolynomial.monomial u f)=fun zp => angularMoment u*f zp := by
  classical
  by_cases hf : f=0
  · subst f
    simp [average]
    rfl
  · simp [average,MvPolynomial.support_monomial,hf]

theorem average_constant (f : Symbol) : average (MvPolynomial.C f)=fun zp => f zp/2 := by
  change average (MvPolynomial.monomial 0 f)=_
  rw [average_monomial,angularMoment_zero]
  funext zp
  ring

theorem scalarJordan_originalLeaf_grouped (r : ℕ) (d e : Fin 3) (j k : Fin 14) (zp : Phase)
    (physical : zp∈originalPhysicalPhase) :
    (scalarJordan r (originalLeaf d j) (originalLeaf e k) zp : ℂ)=
      (originalGroupedN0Coefficient r d e j k zp+originalGroupedN0Coefficient r e d k j zp)/2 := by
  rw [scalarJordan_native]
  change (originalN0Coefficient r d e j k zp+originalN0Coefficient r e d k j zp)/2=_
  rw [originalN0Coefficient_grouped r d e j k zp physical,
    originalN0Coefficient_grouped r e d k j zp physical]

end LowEnergy.PreparationVacuumEngineSource
