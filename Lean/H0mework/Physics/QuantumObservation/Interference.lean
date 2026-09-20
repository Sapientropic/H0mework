import H0mework.Physics.QuantumState.StateSource

/-! The two paths are restrictions of the actual Dirac spin components.
Their exclusive additive response deletes only the upper/lower coherence. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Observation

open Matrix State ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair
open scoped ComplexOrder

noncomputable section

def upperVector (point : BasePoint) (index : Source.Index) : ℂ :=
  if index.1 < 2 then Source.vector point index else 0

def lowerVector (point : BasePoint) (index : Source.Index) : ℂ :=
  if index.1 < 2 then 0 else Source.vector point index

theorem paths_reconstruct (point : BasePoint) :
    upperVector point + lowerVector point = Source.vector point := by
  funext index
  simp only [Pi.add_apply, upperVector, lowerVector]
  split_ifs <;> simp

theorem upper_inner_self (point : BasePoint) :
    (∑ i, star (upperVector point i) * upperVector point i) = (1 / 2 : ℂ) := by
  simp only [Fintype.sum_prod_type]
  simp [upperVector, Source.vector, Source.amplitude, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two]
  norm_num only [map_ofNat]
  have norm := Source.phase_star_mul frequency point
  change (starRingEnd ℂ) (upperPhase point) * upperPhase point = 1 at norm
  linear_combination norm / 2

theorem lower_inner_self (point : BasePoint) :
    (∑ i, star (lowerVector point i) * lowerVector point i) = (1 / 2 : ℂ) := by
  simp only [Fintype.sum_prod_type]
  simp [lowerVector, Source.vector, Source.amplitude, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two]
  norm_num only [map_ofNat]
  have norm := Source.phase_star_mul (-frequency) point
  change (starRingEnd ℂ) (lowerPhase point) * lowerPhase point = 1 at norm
  linear_combination norm / 2

def dephasedDensity (point : BasePoint) : Observable :=
  pureMatrix (upperVector point) + pureMatrix (lowerVector point)

def exclusiveEvaluation (point : BasePoint) : Observable →ₗ[ℂ] ℂ :=
  vectorEvaluation (upperVector point) + vectorEvaluation (lowerVector point)

theorem dephasedDensity_posSemidef (point : BasePoint) :
    (dephasedDensity point).PosSemidef :=
  (pureMatrix_posSemidef _).add (pureMatrix_posSemidef _)

theorem dephasedDensity_trace (point : BasePoint) : (dephasedDensity point).trace = 1 := by
  rw [dephasedDensity, Matrix.trace_add, pureMatrix_trace, pureMatrix_trace,
    upper_inner_self, lower_inner_self]
  norm_num

theorem dephasedDensity_entries (point : BasePoint) (i j : Source.Index) :
    dephasedDensity point i j =
      if (i.1 < 2 ↔ j.1 < 2) then density point i j else 0 := by
  rw [density_eq_pureMatrix]
  by_cases hi : i.1 < 2 <;> by_cases hj : j.1 < 2 <;>
    simp [dephasedDensity, pureMatrix, vecMulVec, upperVector, lowerVector, hi, hj]

theorem exclusiveEvaluation_positive (point : BasePoint) (A : Observable)
    (hA : A.PosSemidef) : 0 ≤ exclusiveEvaluation point A :=
  add_nonneg (vectorEvaluation_positive _ _ hA) (vectorEvaluation_positive _ _ hA)

theorem exclusiveEvaluation_eq_trace (point : BasePoint) (A : Observable) :
    exclusiveEvaluation point A = (dephasedDensity point * A).trace := by
  simp only [exclusiveEvaluation, LinearMap.add_apply, vectorEvaluation_eq_trace,
    dephasedDensity, add_mul, Matrix.trace_add]

theorem exclusiveEvaluation_one (point : BasePoint) : exclusiveEvaluation point 1 = 1 := by
  rw [exclusiveEvaluation_eq_trace, Matrix.mul_one, dephasedDensity_trace]

def coherentWeight (point : BasePoint) : ℝ := effectWeight point (sourceEffect 0)

def exclusiveWeight (point : BasePoint) : ℝ :=
  (exclusiveEvaluation point (sourceEffect 0).matrix).re

theorem coherent_overlap (point : BasePoint) :
    star (Source.vector 0) ⬝ᵥ Source.vector point =
      (upperPhase point + lowerPhase point) / 2 := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, Source.vector_zero]
  simp [Source.vector, Source.amplitude, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem upper_overlap (point : BasePoint) :
    star (Source.vector 0) ⬝ᵥ upperVector point = upperPhase point / 2 := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, Source.vector_zero]
  simp [upperVector, Source.vector, Source.amplitude, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem lower_overlap (point : BasePoint) :
    star (Source.vector 0) ⬝ᵥ lowerVector point = lowerPhase point / 2 := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, Source.vector_zero]
  simp [lowerVector, Source.vector, Source.amplitude, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem coherentWeight_formula (point : BasePoint) :
    coherentWeight point = Complex.normSq ((upperPhase point + lowerPhase point) / 2) := by
  rw [coherentWeight, effectWeight_sourceEffect, coherent_overlap]

theorem exclusiveWeight_formula (point : BasePoint) : exclusiveWeight point = 1 / 2 := by
  change (vectorEvaluation (upperVector point) (pureMatrix (Source.vector 0)) +
    vectorEvaluation (lowerVector point) (pureMatrix (Source.vector 0))).re = _
  rw [vectorEvaluation_pureMatrix, vectorEvaluation_pureMatrix, upper_overlap, lower_overlap]
  simp only [Complex.add_re, Complex.ofReal_re, map_div₀]
  dsimp only [upperPhase, lowerPhase]
  rw [Source.phase_normSq frequency point, Source.phase_normSq (-frequency) point]
  norm_num

theorem coherentWeight_zero : coherentWeight 0 = 1 := effectWeight_sourceEffect_self 0

/-- Exclusive alternatives with these actual path restrictions cannot reproduce
the coherent state's response to every effect. -/
def ClassicalExclusivePaths (point : BasePoint) : Prop :=
  ∀ effect : Effect, evaluation point effect.matrix = exclusiveEvaluation point effect.matrix

theorem source_interference :
    coherentWeight 0 = 1 ∧ exclusiveWeight 0 = 1 / 2 ∧
      coherentWeight 0 ≠ exclusiveWeight 0 := by
  rw [coherentWeight_zero, exclusiveWeight_formula]
  norm_num

theorem not_classicalExclusivePaths : ¬ ClassicalExclusivePaths 0 := by
  intro additive
  have test := congrArg Complex.re (additive (sourceEffect 0))
  exact source_interference.2.2 test

theorem source_density_ne_dephased : density 0 ≠ dephasedDensity 0 := by
  intro same
  apply not_classicalExclusivePaths
  intro effect
  rw [evaluation_eq_trace, same, ← exclusiveEvaluation_eq_trace]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Observation
