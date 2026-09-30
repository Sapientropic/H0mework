import H0mework.Realization.Operations.FiniteKernel
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! The actual finite free material action generates its own recurrence coefficients. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.MaterialRecurrence

open Polynomial

noncomputable section

universe r u

variable {R : Type r} [CommRing R] [Nontrivial R]
variable {C : Type u} [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
variable (action : C →ₗ[R] C)

def bound : Nat := action.charpoly.natDegree
def relation : R[X] := X * action.charpoly
def coefficients : Fin (bound action + 1) → R := fun index => -(relation action).coeff index.val

omit [Nontrivial R] in
theorem relation_monic : (relation action).Monic := monic_X.mul action.charpoly_monic

theorem relation_degree : (relation action).natDegree = bound action + 1 :=
  natDegree_X_mul action.charpoly_monic.ne_zero

omit [Nontrivial R] in
theorem relation_zero : aeval action (relation action) = 0 := by
  rw [relation, map_mul, action.aeval_self_charpoly, mul_zero]

theorem power_generated : action ^ (bound action + 1) =
    ∑ index : Fin (bound action + 1), coefficients action index • (action ^ index.val) := by
  have generated := congrArg (aeval action) (relation_monic action).as_sum
  rw [relation_zero, relation_degree] at generated
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul] at generated
  have leading := eq_neg_of_add_eq_zero_left generated.symm
  have reindex := Fin.sum_univ_eq_sum_range
    (fun index => -((relation action).coeff index) • (action ^ index)) (bound action + 1)
  apply (show action ^ (bound action + 1) =
      ∑ index ∈ Finset.range (bound action + 1), -((relation action).coeff index) • (action ^ index) from
        by simpa only [Finset.sum_neg_distrib, neg_smul] using leading).trans
  exact reindex.symm

variable {B : Type u} [AddCommGroup B] [Module R B] (observation : C →ₗ[R] B)

theorem observation_law : observation.comp (action ^ (bound action + 1)) =
    ∑ index : Fin (bound action + 1), coefficients action index • stageEvaluator action observation index.val := by
  rw [power_generated]
  apply LinearMap.ext
  intro value
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]
  apply Finset.sum_congr rfl
  intro index _
  rfl

end
end SourceGeneratedActionObservationHistory.MaterialRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
