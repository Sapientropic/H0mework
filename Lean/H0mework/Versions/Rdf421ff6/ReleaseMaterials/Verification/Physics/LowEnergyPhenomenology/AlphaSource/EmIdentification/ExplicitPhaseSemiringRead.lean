import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ExplicitPhaseDoubleCarrier
import Mathlib.Algebra.Polynomial.Smeval

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
open Polynomial
open scoped TensorProduct

private def quotientAction {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) : AdjoinRoot P →ₗ[ℂ] A :=
  (aeval T).toLinearMap.comp (AdjoinRoot.modByMonicHom monic)

private theorem quotient_action_mk {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) (annihilated : aeval T P = 0) (Q : ℂ[X]) :
    quotientAction P monic T (AdjoinRoot.mk P Q) = aeval T Q := by
  have relation := congrArg (aeval T) (modByMonic_add_div Q P)
  rw [map_add, map_mul, annihilated, zero_mul, add_zero] at relation
  change aeval T (AdjoinRoot.modByMonicHom monic (AdjoinRoot.mk P Q)) = _
  rw [AdjoinRoot.modByMonicHom_mk]
  exact relation

private def quotientSemiringRead {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) (annihilated : aeval T P = 0) : AdjoinRoot P →ₐ[ℂ] A :=
  AlgHom.ofLinearMap (quotientAction P monic T)
    (by
      have actual := quotient_action_mk P monic T annihilated 1
      simpa only [map_one] using actual)
    (by
      intro a b
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective b
      rw [← map_mul, quotient_action_mk P monic T annihilated,
        quotient_action_mk P monic T annihilated, quotient_action_mk P monic T annihilated, map_mul])

private theorem quotient_semiring_mk {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) (annihilated : aeval T P = 0) (Q : ℂ[X]) :
    quotientSemiringRead P monic T annihilated (AdjoinRoot.mk P Q) = aeval T Q :=
  quotient_action_mk P monic T annihilated Q

private theorem quotient_semiring_root {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) (annihilated : aeval T P = 0) :
    quotientSemiringRead P monic T annihilated (AdjoinRoot.root P) = T := by
  rw [← AdjoinRoot.mk_X, quotient_semiring_mk, aeval_X]

private theorem polynomial_evaluations_commute {A : Type*} [Semiring A] [Algebra ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (x y : A) (commutes : Commute x y) (P Q : ℂ[X]) : Commute (aeval x P) (aeval y Q) := by
  rw [aeval_eq_smeval, aeval_eq_smeval]
  exact smeval_commute ℂ P Q commutes

private def commutingDoubleRead {A : Type*} [Semiring A] [Algebra ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) (x y : A)
    (hx : aeval x P = 0) (hy : aeval y Q = 0) (commutes : Commute x y) : DoubleCarrier P Q →ₐ[ℂ] A :=
  Algebra.TensorProduct.lift (quotientSemiringRead P hP x hx) (quotientSemiringRead Q hQ y hy)
    (by
      intro a b
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective b
      rw [quotient_semiring_mk, quotient_semiring_mk]
      exact polynomial_evaluations_commute x y commutes f g)

/-- The generated double-carrier coefficients read the actual commuting semiring directly. -/
theorem explicit_commuting_phase_annihilated {A : Type*} [Semiring A] [Algebra ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) (x y : A)
    (hx : aeval x P = 0) (hy : aeval y Q = 0) (commutes : Commute x y) :
    aeval (Complex.I • x + (-Complex.I) • y) (explicitPhasePolynomial P Q) = 0 := by
  let read := commutingDoubleRead P Q hP hQ x y hx hy commutes
  have phase : read (phaseElement P Q) = Complex.I • x + (-Complex.I) • y := by
    simp only [read, commutingDoubleRead, phaseElement, map_add, map_smul,
      Algebra.TensorProduct.lift_tmul, quotient_semiring_root, map_one, mul_one, one_mul]
  have actual := congrArg read (double_phase_annihilated P Q hP hQ)
  rw [← Polynomial.aeval_algHom_apply, phase, map_zero] at actual
  exact actual

theorem semiring_linear_factor {A : Type*} [Semiring A] [Algebra ℂ A] (T : A) (lambda : ℂ) :
    aeval T (X-C lambda) = T + (-lambda) • (1 : A) := by
  have polynomial : (X-C lambda : ℂ[X]) = X+C (-lambda) := by simp only [C_neg, sub_eq_add_neg]
  rw [polynomial, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- Synthetic division is mapped as an additive polynomial identity, avoiding target Ring projections. -/
theorem semiring_polynomial_pencil {A : Type*} [Semiring A] [Algebra ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (T : A) (P : ℂ[X]) (lambda : ℂ) (annihilated : aeval T P = 0) :
    (lambda • (1 : A) + (-1 : ℂ) • T) * aeval T (P /ₘ (X-C lambda)) = P.eval lambda • (1 : A) := by
  have divide := modByMonic_add_div P (X-C lambda)
  rw [modByMonic_X_sub_C_eq_C_eval] at divide
  have polynomial : (C lambda+C (-1)*X) * (P /ₘ (X-C lambda)) + P = C (P.eval lambda) := by
    simp only [C_neg, C_1]
    linear_combination -divide
  have actual := congrArg (aeval T) polynomial
  simpa only [map_add, map_mul, aeval_C, aeval_X, annihilated, add_zero,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using actual

theorem scalar_pencil_neg {A : Type*} [AddCommGroup A] [Module ℂ A] (T U : A) (lambda : ℂ) :
    T+(-lambda) • U = -(lambda • U-T) := by
  simp only [neg_smul, sub_eq_add_neg, neg_add_rev, neg_neg]

theorem scalar_pencil_add {A : Type*} [AddCommGroup A] [Module ℂ A] (T U : A) (lambda : ℂ) :
    lambda • U-T = lambda • U+(-1 : ℂ) • T := by
  simp only [neg_one_smul, sub_eq_add_neg]

theorem scalar_negative_unit {A : Type*} [Semiring A] [Algebra ℂ A] (T : A) (unit : IsUnit T) :
    IsUnit ((-1 : ℂ) • T) := by
  have scalar : IsUnit (algebraMap ℂ A (-1)) :=
    (isUnit_iff_ne_zero.mpr (by simp : (-1 : ℂ) ≠ 0)).map (algebraMap ℂ A)
  exact (Algebra.smul_def (-1 : ℂ) T) ▸ scalar.mul unit

theorem normalized_polynomial_inverse {A : Type*} [Semiring A] [Algebra ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (T N : A) (c : ℂ) (relation : T*N=c • (1 : A)) (nonzero : c ≠ 0) :
    T*(c⁻¹ • N)=1 := by
  rw [mul_smul_comm, relation, smul_smul, inv_mul_cancel₀ nonzero, one_smul]

end LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
