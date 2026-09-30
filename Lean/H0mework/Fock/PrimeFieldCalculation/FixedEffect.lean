import H0mework.Fock.PrimeFieldCalculation.FixedMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFixedInventoryRecovery

open SourcePrimeHistoryRecovery SourceGeneratedAcquisitionContinuation
open SourceConditionalInventory SourceUniformFibreVariance
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

local instance effectObservationMeasurable (width : Nat) : MeasurableSpace (Observation width) := ⊤

private theorem bound_two : inventoryBound (runtimeAt 2) = 2 :=
  (inventory_bound (runtimeAt 2)).trans (runtimeAt_state 2)

private def first : Fin (inventoryBound (runtimeAt 2) + 1) := ⟨0, by rw [bound_two]; decide⟩
private def second : Fin (inventoryBound (runtimeAt 2) + 1) := ⟨1, by rw [bound_two]; decide⟩
private def seven : Nat.Primes := ⟨7, by decide⟩
private def eleven : Nat.Primes := ⟨11, by decide⟩

private theorem first_read (width : Nat) (actor : Fin (inventoryBound (runtimeAt 2) + 1)) :
    primeRead seven (query (runtimeAt 2) width actor 0) = if 1 ≤ actor.val then 1 else 0 := by
  have actual := (congrArg (primeRead seven) (query_value (runtimeAt 2) width actor 0)).trans
    (primeRead_source seven (actor.val + 1 + (0 : Fin (width + 1)).val))
  change _ = if 7 ≤ 2 * (actor.val + 1 + 0 + 2) then 1 else 0 at actual
  have same : 7 ≤ 2 * (actor.val + 1 + 0 + 2) ↔ 1 ≤ actor.val := by omega
  simpa only [same] using actual

private theorem last_read (actor : Fin (inventoryBound (runtimeAt 2) + 1)) :
    primeRead eleven (query (runtimeAt 2) 1 actor 1) = if 2 ≤ actor.val then 1 else 0 := by
  have actual := (congrArg (primeRead eleven) (query_value (runtimeAt 2) 1 actor 1)).trans
    (primeRead_source eleven (actor.val + 1 + (1 : Fin 2).val))
  change _ = if 11 ≤ 2 * (actor.val + 1 + 1 + 2) then 1 else 0 at actual
  have same : 11 ≤ 2 * (actor.val + 1 + 1 + 2) ↔ 2 ≤ actor.val := by omega
  simpa only [same] using actual

private theorem two_column_injective : Function.Injective (query (runtimeAt 2) 1) := by
  intro left right same
  have firstSame := (first_read 1 left).symm.trans
    ((congrArg (fun row => primeRead seven (row 0)) same).trans (first_read 1 right))
  have lastSame := (last_read left).symm.trans
    ((congrArg (fun row => primeRead eleven (row 1)) same).trans (last_read right))
  have lc := left.isLt
  have rc := right.isLt
  have bound := bound_two
  apply Fin.ext
  split_ifs at firstSame lastSame <;> norm_num at * <;> omega

private theorem tail_same (actor : Fin (inventoryBound (runtimeAt 2) + 1)) (last : actor.val = 2) :
    query (runtimeAt 2) 0 actor = query (runtimeAt 2) 0 second := by
  funext time
  rw [query_value, query_value]
  have zero : time.val = 0 := by omega
  change rawField (actor.val + 1 + time.val) = rawField (1 + 1 + time.val)
  rw [last, zero]
  exact SourceGeneratedConditionalInventory.unchanged_snapshot 2 (by decide)

private theorem two_outputs : outputs (inventoryBound (runtimeAt 2)) (query (runtimeAt 2) 0) =
    {query (runtimeAt 2) 0 first, query (runtimeAt 2) 0 second} := by
  ext value
  simp only [outputs, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨actor, rfl⟩
    have inside := actor.isLt
    have bound := bound_two
    have cases : actor.val = 0 ∨ actor.val = 1 ∨ actor.val = 2 := by omega
    rcases cases with a | b | c
    · exact Or.inl (congrArg (query (runtimeAt 2) 0) (Fin.ext a))
    · exact Or.inr (congrArg (query (runtimeAt 2) 0) (Fin.ext b))
    · exact Or.inr (tail_same actor c)
  · rintro (same | same)
    · exact ⟨first, same.symm⟩
    · exact ⟨second, same.symm⟩

private theorem outputs_differ : query (runtimeAt 2) 0 first ≠ query (runtimeAt 2) 0 second := by
  intro same
  have read := (first_read 0 first).symm.trans
    ((congrArg (fun row => primeRead seven (row 0)) same).trans (first_read 0 second))
  norm_num [first, second] at read

theorem actual_prefix_recovery : costAt (runtimeAt 2) 0 = 1 ∧ costAt (runtimeAt 2) 1 = 0 := by
  refine ⟨?_, exact_inventory _ _ two_column_injective⟩
  unfold costAt
  rw [cost_eq, two_outputs, Finset.card_pair outputs_differ, bound_two]
  norm_num

end
end SourceFixedInventoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
