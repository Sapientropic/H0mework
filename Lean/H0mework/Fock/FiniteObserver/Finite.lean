import H0mework.Fock.FiniteObserver.Word

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def finiteRead (bound : Nat) (coefficients : Fin (bound + 1) → ℂ) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (∑ actor, Finsupp.single actor.val (coefficients actor))

theorem finite_action (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Fin (inventoryBound runtime + steps + 1) → ℂ) :
    SourceCopyGraph.action (inventoryBound runtime) index (finiteRead (inventoryBound runtime + steps) coefficients) =
      ∑ actor, coefficients actor • SourceColumnForcing.column (inventoryBound runtime) index actor.val := by
  simp only [finiteRead, map_sum]
  apply Finset.sum_congr rfl
  intro actor _
  rw [show Finsupp.single actor.val (coefficients actor) = coefficients actor • Finsupp.single actor.val (1 : ℂ) by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul]
  rfl

theorem finite_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Fin (inventoryBound runtime + steps + 1) → ℂ) (actor : Fin (inventoryBound runtime + steps + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
      SourceCopyGraph.action (inventoryBound runtime) index (finiteRead (inventoryBound runtime + steps) coefficients)⟫_ℂ =
      coefficients actor + (∑ source, coefficients source) +
        ((index.val + 1 : Nat) : ℂ)^2 * ((actor.val + 1 : Nat) : ℂ) *
          (∑ source, ((source.val + 1 : Nat) : ℂ) * coefficients source) := by
  classical
  rw [finite_action, inner_sum]
  simp only [inner_smul_right, physical_gram]
  calc
    _ = ∑ source, ((if actor = source then coefficients source else 0) + coefficients source +
        ((index.val + 1 : Nat) : ℂ)^2 * ((actor.val + 1 : Nat) : ℂ) *
          (((source.val + 1 : Nat) : ℂ) * coefficients source)) := by
      apply Finset.sum_congr rfl
      intro source _
      by_cases same : actor = source
      · subst source
        simp only [ite_true]
        ring
      · have distinct : actor.val ≠ source.val := fun equality => same (Fin.ext equality)
        simp only [if_neg same, if_neg distinct]
        ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]

theorem calculated_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (word : Nat →₀ ℚ) (actor : Fin (inventoryBound runtime + steps + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
      SourceCopyGraph.action (inventoryBound runtime) index
        (finiteRead (inventoryBound runtime + steps) (fun source => (calculate (inventoryBound runtime + steps) (index.val + 1) word source : ℂ)))⟫_ℂ =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
        SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord word)⟫_ℂ := by
  rw [finite_pairing, ← response_source]
  have equation := congrArg (fun value : ℚ => (value : ℂ))
    (solve_equation (inventoryBound runtime + steps) (index.val + 1) (response (inventoryBound runtime + steps) (index.val + 1) word) actor)
  simpa only [calculate, weight, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_sum, Rat.cast_natCast, Rat.cast_one] using equation

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
