import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Gaussian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel ContinuousGradient
open scoped BigOperators

theorem orbital_continuous (centre : Point) (mode : Nat) (jet : MultiIndex) :
    Continuous (orbitalValue centre mode jet) :=
  Complex.continuous_ofReal.comp
    ((SourceGaussianModel.orbital_contDiff [primitive mode] jet 0).continuous.comp
      (continuous_id.sub continuous_const))

theorem orbital_line (centre : Point) (mode : Nat) (t : ℝ) :
    orbitalValue centre mode 0 (Function.update centre 0 (centre 0 + t)) =
      (t : ℂ)^mode * (Real.exp (-(t^2)) : ℂ) := by
  simp [orbitalValue,SourceGaussianModel.orbital,SourceGaussianModel.value,
    SourceGaussianModel.factor,SourceGaussianModel.jetPoly,primitive,
    GaussianPrimitive.gaussian,Function.update]

theorem orbital_values_independent (centre : Point) (n : Nat) :
    LinearIndependent ℂ (fun i : Fin n => orbitalValue centre i.val 0) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coeff zero i
  have lineZero (t : ℝ) : ∑ j : Fin n, coeff j * (t : ℂ)^j.val = 0 := by
    have atLine := congrFun zero (Function.update centre 0 (centre 0+t))
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,orbital_line,
      ← mul_assoc] at atLine
    rw [← Finset.sum_mul] at atLine
    exact (mul_eq_zero.mp atLine).resolve_right
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  let polynomial : Polynomial ℂ := ∑ j : Fin n, Polynomial.C (coeff j) * Polynomial.X^j.val
  have evaluated (t : ℝ) : polynomial.eval (t : ℂ) = 0 := by
    simpa [polynomial,Polynomial.eval_finsetSum] using lineZero t
  have polynomialZero : polynomial = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot polynomial
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro z ⟨t,rfl⟩
    exact evaluated t
  have coefficient := congrArg (fun p : Polynomial ℂ => p.coeff i.val) polynomialZero
  simpa [polynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow,Fin.val_inj] using coefficient

/-- The common continuous source representative recovers exact zero from an L² finite relation. -/
theorem field_combination_zero (centre : Point) (n : Nat) (coeff : Fin n → ℂ)
    (zero : (∑ i : Fin n, coeff i • orbitalField centre i.val 0) = 0) :
    (fun x : Point => ∑ i : Fin n, coeff i * orbitalValue centre i.val 0 x) = 0 := by
  classical
  have each (i : Fin n) :
      (fun x : Point => (coeff i • orbitalField centre i.val 0) x) =ᵐ[volume]
        fun x => coeff i * orbitalValue centre i.val 0 x := by
    filter_upwards [Lp.coeFn_smul (coeff i) (orbitalField centre i.val 0),
      orbital_field_source centre i.val 0] with x smulSource orbitalSource
    simpa only [Pi.smul_apply,smul_eq_mul,orbitalSource] using smulSource
  have sumSource : (fun x : Point => (∑ i : Fin n, coeff i • orbitalField centre i.val 0) x) =ᵐ[volume]
      fun x => ∑ i : Fin n, (coeff i • orbitalField centre i.val 0) x := by
    simpa using Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin n))
      (fun i => coeff i • orbitalField centre i.val 0)
  have almostZero : (fun x : Point => ∑ i : Fin n, coeff i * orbitalValue centre i.val 0 x) =ᵐ[volume]
      (0 : Point → ℂ) := by
    filter_upwards [sumSource,Filter.eventually_all.mpr each,Lp.coeFn_zero ℂ 2 (volume : Measure Point)]
      with x sumAt eachAt zeroAt
    have combined : (∑ i : Fin n, coeff i * orbitalValue centre i.val 0 x) =
        ∑ i : Fin n, (coeff i • orbitalField centre i.val 0) x :=
      Finset.sum_congr rfl (fun i _ => (eachAt i).symm)
    rw [zero] at sumAt
    exact combined.trans (sumAt.symm.trans zeroAt)
  have continuous : Continuous (fun x : Point => ∑ i : Fin n, coeff i * orbitalValue centre i.val 0 x) :=
    continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul (orbital_continuous centre i.val 0))
  exact (Continuous.ae_eq_iff_eq (volume : Measure Point) continuous continuous_const).mp almostZero

theorem orbitals_independent (centre : Point) (n : Nat) :
    LinearIndependent ℂ (fun i : Fin n => orbitalField centre i.val 0) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coeff zero i
  have functionZero : (∑ j : Fin n, coeff j • orbitalValue centre j.val 0) = 0 := by
    ext x
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using
      congrFun (field_combination_zero centre n coeff zero) x
  exact (Fintype.linearIndependent_iff.mp (orbital_values_independent centre n)) coeff functionZero i

end
end CPS1ElectronicSource
