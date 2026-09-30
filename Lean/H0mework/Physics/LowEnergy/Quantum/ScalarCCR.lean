import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! Polynomial-domain canonical scalar coordinates.  The original source
kinetic form supplies the Hamiltonian coefficients; these operators supply
the quantum coordinate/momentum algebra without selecting a vacuum. -/
set_option autoImplicit false
namespace SourceScalarCCR
noncomputable section
variable {σ : Type*}

abbrev BosonSpace (σ : Type*) := MvPolynomial σ ℂ
abbrev BosonEnd (σ : Type*) := Module.End ℂ (BosonSpace σ)

def position (i : σ) : BosonEnd σ := LinearMap.mulLeft ℂ (MvPolynomial.X i)

def momentum (i : σ) : BosonEnd σ :=
  (-Complex.I) • (MvPolynomial.pderiv i).toLinearMap

theorem position_apply (i : σ) (f : BosonSpace σ) :
    position i f = MvPolynomial.X i * f := rfl

theorem momentum_apply (i : σ) (f : BosonSpace σ) :
    momentum i f = (-Complex.I) • MvPolynomial.pderiv i f := rfl

theorem position_position (i j : σ) :
    position i * position j = position j * position i := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, position_apply]
  ring

theorem position_momentum [DecidableEq σ] (i j : σ) :
    position i * momentum j - momentum j * position i =
      (if i = j then Complex.I else 0) • (1 : BosonEnd σ) := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.sub_apply, Module.End.mul_apply, position_apply,
    momentum_apply, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
    LinearMap.smul_apply, Module.End.one_apply]
  by_cases same : i = j
  · subst j
    simp only [Pi.single_eq_same, if_true, one_mul, smul_add, mul_smul_comm]
    module
  · simp [same]

theorem pderiv_commute (i j : σ) (f : BosonSpace σ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.pderiv_C, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f k hf =>
      simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X]
      by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp_all

theorem momentum_momentum (i j : σ) :
    momentum i * momentum j = momentum j * momentum i := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, momentum_apply, map_smul, pderiv_commute i j]

end
end SourceScalarCCR
