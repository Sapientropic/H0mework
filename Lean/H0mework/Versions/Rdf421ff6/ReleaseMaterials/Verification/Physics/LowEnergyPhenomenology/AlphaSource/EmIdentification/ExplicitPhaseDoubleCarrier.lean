import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
open Polynomial
open scoped TensorProduct Matrix BigOperators

abbrev DoubleCarrier (P Q : ℂ[X]) := AdjoinRoot P ⊗[ℂ] AdjoinRoot Q
abbrev DoubleIndex (P Q : ℂ[X]) := Fin P.natDegree × Fin Q.natDegree

def doubleBasis (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) :
    Module.Basis (DoubleIndex P Q) ℂ (DoubleCarrier P Q) :=
  (AdjoinRoot.powerBasisAux' hP).tensorProduct (AdjoinRoot.powerBasisAux' hQ)

def phaseElement (P Q : ℂ[X]) : DoubleCarrier P Q :=
  Complex.I • (AdjoinRoot.root P ⊗ₜ[ℂ] (1 : AdjoinRoot Q)) +
    (-Complex.I) • ((1 : AdjoinRoot P) ⊗ₜ[ℂ] AdjoinRoot.root Q)

/-- Explicit remainder coefficients: multiplication by X in the monic quotient. -/
abbrev companionCoefficients (P : ℂ[X]) : Matrix (Fin P.natDegree) (Fin P.natDegree) ℂ :=
  fun i j => ((X * X^j.val) %ₘ P).coeff i.val

/-- The coefficient algorithm uses only the two input polynomials. -/
def phaseCoefficientMatrix (P Q : ℂ[X]) : Matrix (DoubleIndex P Q) (DoubleIndex P Q) ℂ :=
  fun i j => (if i.2 = j.2 then Complex.I * companionCoefficients P i.1 j.1 else 0) +
    (if i.1 = j.1 then (-Complex.I) * companionCoefficients Q i.2 j.2 else 0)

def explicitPhasePolynomial (P Q : ℂ[X]) : ℂ[X] := (phaseCoefficientMatrix P Q).charpoly

theorem explicit_phase_monic (P Q : ℂ[X]) : (explicitPhasePolynomial P Q).Monic :=
  Matrix.charpoly_monic _

theorem explicit_phase_degree (P Q : ℂ[X]) :
    (explicitPhasePolynomial P Q).natDegree = P.natDegree * Q.natDegree := by
  simp [explicitPhasePolynomial, Matrix.charpoly_natDegree_eq_dim, DoubleIndex]

private theorem companion_coefficients_return (P : ℂ[X]) (hP : P.Monic)
    (i j : Fin P.natDegree) :
    (AdjoinRoot.powerBasisAux' hP).repr
      (AdjoinRoot.root P * (AdjoinRoot.powerBasisAux' hP) j) i = companionCoefficients P i j := by
  rw [(show (AdjoinRoot.powerBasisAux' hP) j = AdjoinRoot.root P^j.val from
    (AdjoinRoot.powerBasis' hP).basis_eq_pow j)]
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    AdjoinRoot.modByMonicHom_mk]

/-- The explicit matrix is the actual regular representation of the source phase. -/
theorem phase_coefficient_matrix_return (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) :
    phaseCoefficientMatrix P Q = Algebra.leftMulMatrix (doubleBasis P Q hP hQ) (phaseElement P Q) := by
  ext i j
  rcases i with ⟨ip, iq⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  unfold phaseCoefficientMatrix phaseElement doubleBasis companionCoefficients
  have basis_j := Module.Basis.tensorProduct_apply'
    (AdjoinRoot.powerBasisAux' hP) (AdjoinRoot.powerBasisAux' hQ) j
  rw [basis_j]
  simp only [ add_mul, smul_mul_assoc, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply,Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self,
    companion_coefficients_return, smul_eq_mul]
  by_cases first : ip = j.1 <;> by_cases second : iq = j.2 <;>
    simp [first, second, eq_comm, mul_comm, companionCoefficients]

theorem double_phase_annihilated (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) :
    aeval (phaseElement P Q) (explicitPhasePolynomial P Q) = 0 := by
  apply Algebra.leftMulMatrix_injective (doubleBasis P Q hP hQ)
  rw [← Polynomial.aeval_algHom_apply, map_zero, ← phase_coefficient_matrix_return]
  exact Matrix.aeval_self_charpoly _

private def quotientRead {S : Type*} [CommRing S] [Algebra ℂ S]
    (P : ℂ[X]) (x : S) (hx : aeval x P = 0) : AdjoinRoot P →ₐ[ℂ] S :=
  AdjoinRoot.liftAlgHom P (Algebra.ofId ℂ S) x hx

private def doubleRead {S : Type*} [CommRing S] [Algebra ℂ S]
    (P Q : ℂ[X]) (x y : S) (hx : aeval x P = 0) (hy : aeval y Q = 0) :
    DoubleCarrier P Q →ₐ[ℂ] S :=
  Algebra.TensorProduct.lift (quotientRead P x hx) (quotientRead Q y hy)
    (fun _ _ => (Commute.all _ _))

private theorem double_read_phase {S : Type*} [CommRing S] [Algebra ℂ S]
    (P Q : ℂ[X]) (x y : S) (hx : aeval x P = 0) (hy : aeval y Q = 0) :
    doubleRead P Q x y hx hy (phaseElement P Q) = Complex.I • x + (-Complex.I) • y := by
  simp [doubleRead, quotientRead, phaseElement, map_smul, AdjoinRoot.liftAlgHom_root]

/-- Source annihilators generate this finite coefficient polynomial for the actual phase sum. -/
theorem explicit_phase_annihilated {S : Type*} [CommRing S] [Algebra ℂ S]
    (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (x y : S) (hx : aeval x P = 0) (hy : aeval y Q = 0) :
    aeval (Complex.I • x + (-Complex.I) • y) (explicitPhasePolynomial P Q) = 0 := by
  have generated := congrArg (doubleRead P Q x y hx hy) (double_phase_annihilated P Q hP hQ)
  rw [← Polynomial.aeval_algHom_apply, double_read_phase, map_zero] at generated
  exact generated

/-- Strip exactly the finite multiplicity at the evaluation clock, using only polynomial coefficients. -/
def poleFreePolynomial (P : ℂ[X]) (lambda : ℂ) : ℂ[X] :=
  P /ₘ (X-C lambda)^P.rootMultiplicity lambda

theorem pole_free_monic (P : ℂ[X]) (monic : P.Monic) (lambda : ℂ) :
    (poleFreePolynomial P lambda).Monic := by
  have factor := P.pow_mul_divByMonic_rootMultiplicity_eq lambda
  exact ((monic_X_sub_C lambda).pow _).of_mul_monic_left (factor ▸ monic)

theorem pole_free_denominator (P : ℂ[X]) (monic : P.Monic) (lambda : ℂ) :
    (poleFreePolynomial P lambda).eval lambda ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero lambda monic.ne_zero

/-- Actual invertibility cancels source quotient modes at lambda without supplying a final denominator. -/
theorem pole_free_annihilated {A : Type*} [Semiring A] [Algebra ℂ A]
    (T : A) (P : ℂ[X]) (lambda : ℂ) (annihilated : aeval T P = 0)
    (factor_unit : IsUnit (aeval T (X-C lambda))) :
    aeval T (poleFreePolynomial P lambda) = 0 := by
  have factor := congrArg (aeval T) (P.pow_mul_divByMonic_rootMultiplicity_eq lambda)
  rw [map_mul, map_pow, annihilated] at factor
  exact (factor_unit.pow (P.rootMultiplicity lambda)).mul_right_injective
    (factor.trans (mul_zero _).symm)

end LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
