import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUniformMaterialInverse
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.TensorProduct.Maps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformMaterialCoefficients
open Polynomial
open scoped TensorProduct
abbrev Parameters:=MvPolynomial (Fin 3) ℂ
abbrev CoefficientAlgebra (A : Type*) [AddCommGroup A] [Module ℂ A]:=Parameters⊗[ℂ]A

/-- Evaluation of finite source coefficients; operator multiplication remains noncommutative. -/
def coefficientEval {A : Type*} [Ring A] [Algebra ℂ A] (v : Fin 3→ℂ) : CoefficientAlgebra A→ₐ[ℂ]A :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ A).comp (MvPolynomial.aeval v)) (AlgHom.id ℂ A)
    (fun P B=>by
      change Commute (algebraMap ℂ A (MvPolynomial.eval v P)) B
      exact Algebra.commutes _ _)

@[simp] theorem coefficient_eval_constant {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (A₀ : A) :
    coefficientEval v (Algebra.TensorProduct.includeRight A₀ : CoefficientAlgebra A)=A₀ := by
  simp [coefficientEval,Algebra.TensorProduct.includeRight_apply]

@[simp] theorem coefficient_eval_scalar {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (P : Parameters) :
    coefficientEval v (algebraMap Parameters (CoefficientAlgebra A) P)=algebraMap ℂ A (MvPolynomial.eval v P) := by
  simp [coefficientEval,Algebra.TensorProduct.algebraMap_def,Algebra.TensorProduct.includeLeftRingHom_apply]

@[simp] theorem coefficient_eval_smul {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (P : Parameters) (B : CoefficientAlgebra A) :
    coefficientEval v (P • B)=MvPolynomial.eval v P • coefficientEval v B := by
  have normalized:=congrArg (coefficientEval v) (Algebra.smul_def P B)
  calc
    _=coefficientEval v (algebraMap Parameters (CoefficientAlgebra A) P*B) := normalized
    _=coefficientEval v (algebraMap Parameters (CoefficientAlgebra A) P)*coefficientEval v B :=
      (coefficientEval v).map_mul _ _
    _=_ := by rw [coefficient_eval_scalar];exact (Algebra.smul_def _ _).symm

theorem coefficient_eval_aeval {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (T : CoefficientAlgebra A) (P : Parameters[X]) :
    coefficientEval v (aeval T P)=aeval (coefficientEval v T) (P.map (MvPolynomial.eval v)) := by
  have hom : (coefficientEval v).toRingHom.comp (algebraMap Parameters (CoefficientAlgebra A))=
      (algebraMap ℂ A).comp (MvPolynomial.eval v) := by
    exact RingHom.ext (fun r : Parameters=>coefficient_eval_scalar v r)
  have mapped:=hom_eval₂ (p:=P) (f:=algebraMap Parameters (CoefficientAlgebra A)) (g:=(coefficientEval v).toRingHom) T
  rw [hom] at mapped
  simpa only [aeval_def,eval₂_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using mapped

/-- The same observer reads coefficients before or after source parameter evaluation. -/
def coefficientObserver {A : Type*} [AddCommGroup A] [Module ℂ A] (observer : A→ₗ[ℂ]ℂ) :
    CoefficientAlgebra A→ₗ[ℂ]Parameters :=
  (TensorProduct.AlgebraTensorModule.rid ℂ ℂ Parameters).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : Parameters→ₗ[ℂ]Parameters) observer)

theorem coefficient_observer_eval {A : Type*} [Ring A] [Algebra ℂ A]
    (observer : A→ₗ[ℂ]ℂ) (v : Fin 3→ℂ) (B : CoefficientAlgebra A) :
    MvPolynomial.eval v (coefficientObserver observer B)=observer (coefficientEval v B) := by
  induction B using TensorProduct.induction_on with
  | zero=>simp
  | tmul P A₀=>
    simp [coefficientObserver,coefficientEval,Algebra.algebraMap_eq_smul_one,smul_eq_mul,mul_comm]
  | add B C hB hC=>simp only [map_add,hB,hC]

theorem polynomial_action_natural {R S E F : Type*} [CommRing R] [CommRing S]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
    (f : R→+*S) (read : E→+F) (scalar : ∀r x,read (r • x)=f r • read x)
    (T : Module.End R E) (U : Module.End S F) (step : ∀x,read (T x)=U (read x))
    (P : R[X]) (x : E) : read (aeval T P x)=aeval U (P.map f) (read x) := by
  have power (n : ℕ) (x : E) : read ((T^n) x)=(U^n) (read x) := by
    induction n generalizing x with
    | zero=>simp only [pow_zero,Module.End.one_apply]
    | succ n ih=>simp only [pow_succ',Module.End.mul_apply,step,ih]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ=>simpa only [map_add,Polynomial.map_add,LinearMap.add_apply] using congrArg₂ (·+·) hP hQ
  | monomial n r=>
    simp only [aeval_monomial,Polynomial.map_monomial,Algebra.algebraMap_eq_smul_one,
      Module.End.mul_apply,LinearMap.smul_apply,Module.End.one_apply,scalar,power]

end LowEnergy.GaussComposite.ActualDressedUniformMaterialCoefficients
