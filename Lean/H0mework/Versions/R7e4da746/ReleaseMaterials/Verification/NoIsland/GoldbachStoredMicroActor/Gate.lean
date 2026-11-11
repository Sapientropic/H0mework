import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Stored

set_option autoImplicit false
noncomputable section

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

private theorem exact_stored_micro_pair_carries_the_original_activation
    {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
    {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    history.storedPairAt i = ((runtime.advance i.val).state,(runtime.advance (i.val+1)).state) ∧
    HEq (history.storedActivation i) (runtime.advance i.val).tick ∧
    (history.storedActivation i).nextCurrent = process.stateAt (history.storedPairAt i).2 :=
  ⟨history.stored_pair_actual i,history.stored_activation_actual i,history.stored_successor_actual i⟩

#eval IO.println "CP597_CONTROL + exact_stored_micro_pair_carries_the_original_activation"

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor

open SourceOperationRuntime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored

set_option cleanup.letToHave false in
private theorem fixed_target_bind_and_all_pulses_preserve_actual_material
    (depth count : Nat) (within : count ≤ budget depth) (i : Fin (budget depth+1)) :
    type_of% (stored_seed_material depth) ∧
    type_of% (stored_actor_prefix depth 0 (Nat.zero_le _)) ∧
    type_of% (stored_actor_prefix depth count within) ∧
    (∀ pulse : Nat, (before : pulse < budget depth) → type_of% (stored_actor_increment depth pulse before)) ∧
    type_of% (stored_whole_and_next depth i) :=
  ⟨stored_seed_material depth,stored_actor_prefix depth 0 (Nat.zero_le _),stored_actor_prefix depth count within,
    fun pulse before => stored_actor_increment depth pulse before,stored_whole_and_next depth i⟩

#eval IO.println "CP597_CONTROL + fixed_target_bind_and_all_pulses_preserve_actual_material"

set_option cleanup.letToHave false in
private theorem same_pair_feeds_character_cochain_and_original_inverse
    (depth bound : Nat) (word : Consumer.Formal depth) (stage : Fin (bound+1)) :
    type_of% (stored_character_actual depth bound word stage) ∧
    type_of% (stored_first_cochain depth) ∧
    storedStageInventory (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth)
        ((mathTail depth).run 1) (0 : Fin 1) =
      SourceOperationRuntime.Fibre.firstStage (R := ℤ) (s := Unit.unit)
        (readMaterial depth) (environment depth) (mathTail depth) ∧
    type_of% (Consumer.inverse_receipt depth) :=
  ⟨stored_character_actual depth bound word stage,stored_first_cochain depth,
    stored_inventory_actual (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth)
      ((mathTail depth).run 1) (0 : Fin 1),Consumer.inverse_receipt depth⟩

#eval IO.println "CP597_CONTROL + same_pair_feeds_character_cochain_and_original_inverse"

set_option cleanup.letToHave false in
private theorem stored_terminal_material_feeds_both_original_dispositions_and_receipt (depth : Nat) :
    type_of% (stored_final_value depth) ∧
    type_of% (stored_consumes_original_disposition depth) ∧
    type_of% (Registered.receipt depth) :=
  ⟨stored_final_value depth,stored_consumes_original_disposition depth,Registered.receipt depth⟩

#eval IO.println "CP597_CONTROL + stored_terminal_material_feeds_both_original_dispositions_and_receipt"

private theorem the_stored_unbound_material_cannot_be_an_actor
    (depth : Nat) (point : Registered.Point depth) :
    readMaterial depth ((fullHistory depth).storedPairAt 0).1 ≠ Finsupp.single (some point) 1 := by
  classical
  intro same
  have material := (stored_seed_material depth).symm.trans same
  have atUnbound := congrArg (fun value : Material depth => value none) material
  simp at atUnbound

#eval IO.println "CP597_CONTROL - the_stored_unbound_material_cannot_be_an_actor"
#eval IO.println "CP597_GATE_PASS positive=4 negative=1"

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
