import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Runtime.StoredHistory
import H0mework.Versions.R7e4da746.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Consumer

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored

open SourceOperationEffects SourceOperationRuntime
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Registered
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActuality
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirect
open private someLift_single from
  H0mework.Versions.R7e4da746.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Source

abbrev budget (depth : Nat) := sourceFuel (source depth (emitted depth))

/-- Retain the bind and every pulse of the original fixed-target actor. -/
def fullHistory (depth : Nat) := (mathSeed depth).run (budget depth+1)

theorem stored_seed_material (depth : Nat) :
    readMaterial depth ((fullHistory depth).storedPairAt 0).1 = Finsupp.single none 1 := by
  rw [SourceNativeLivingRootHistoryAt.stored_pair_actual]
  exact seed_material depth

/-- The next stored state retains the same occurrence and complete actor prefix. -/
theorem stored_actor_prefix (depth count : Nat) (within : count ≤ budget depth) :
    readMaterial depth ((fullHistory depth).storedPairAt ⟨count,Nat.lt_succ_of_le within⟩).2 =
      Finsupp.single (some (⟨emitted depth,
        run count (initial (source depth (emitted depth)))⟩ : Registered.Point depth)) 1 := by
  rw [SourceNativeLivingRootHistoryAt.stored_pair_actual]
  exact material_keeps_prefix depth count within

/-- The update inventory uses the two states from the same stored original pulse. -/
theorem stored_actor_increment (depth count : Nat) (within : count < budget depth) :
    storedIncrementEnvironment (readMaterial depth) (environment depth) (fullHistory depth)
      ⟨count+1,by omega⟩ =
    fun _ _ => someLift depth
      (action (index depth) (active depth) (Finsupp.single
        (runPoint (index depth) (active depth) count
          (initialPoint (index depth) (active depth) (emitted depth))) 1) -
      Finsupp.single
        (runPoint (index depth) (active depth) count
          (initialPoint (index depth) (active depth) (emitted depth))) 1) := by
  have environments := stored_environments_actual (readMaterial depth) (environment depth) (fullHistory depth)
    ⟨count+1,Nat.succ_lt_succ within⟩
  exact (congrArg Prod.snd environments).trans (literal_increment_at depth count within)

theorem stored_whole_and_next (depth : Nat) (i : Fin (budget depth+1)) :
    HEq ((fullHistory depth).storedActivation i)
      ((mathSeed depth).advance i.val).tick ∧
    ((fullHistory depth).storedActivation i).nextCurrent =
      (OF.process (old depth) (origin depth) (reader depth)).stateAt ((fullHistory depth).storedPairAt i).2 :=
  ⟨SourceNativeLivingRootHistoryAt.stored_activation_actual (fullHistory depth) i,
    SourceNativeLivingRootHistoryAt.stored_successor_actual (fullHistory depth) i⟩

/-- Existing cofinal character coordinates are evaluated by the actual stored micro states. -/
theorem stored_character_actual (depth bound : Nat) (word : Consumer.Formal depth) (stage : Fin (bound+1)) :
    SourceOperationRuntime.Character.stageRead (readMaterial depth) (environment depth) (mathTail depth) bound
        (Consumer.sourceField depth word) stage =
      storedStageInventory (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth)
        ((mathTail depth).run (bound+1)) stage word := by
  have pair := stored_inventory_actual (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth)
    ((mathTail depth).run (bound+1)) stage
  exact (Consumer.field_reads_actual depth bound word stage).trans
    (congrArg (fun map => map word) pair).symm

theorem stored_first_cochain (depth : Nat) :
    SourceOperationScalarCochain.cochain (R := ℤ) (s := Unit.unit)
      (storedOldEnvironment (readMaterial depth) (environment depth) ((mathTail depth).run 1) 0)
      (storedIncrementEnvironment (readMaterial depth) (environment depth) ((mathTail depth).run 1) 0) =
      Consumer.sourceCochain depth := by
  have actual := stored_environments_actual (runtime := mathTail depth)
    (readMaterial depth) (environment depth) ((mathTail depth).run 1) (0 : Fin 1)
  simp only [Fin.val_zero,LivingRuntimeState.advance] at actual
  have oldRead := congrArg Prod.fst actual
  have effect := congrArg Prod.snd actual
  dsimp only at oldRead effect
  unfold Consumer.sourceCochain
  rw [oldRead,effect]

def storedFinal (depth : Nat) : Material depth :=
  readMaterial depth ((fullHistory depth).storedPairAt (Fin.last (budget depth))).2

theorem stored_final_value (depth : Nat) : storedFinal depth = someLift depth (Registered.calculatedValue depth) := by
  change readMaterial depth ((fullHistory depth).storedPairAt ⟨budget depth,Nat.lt_succ_self _⟩).2 = _
  rw [stored_actor_prefix depth (budget depth) le_rfl,run_source,
    Registered.calculated_value,(Registered.actor depth).rooted.outcome_eq]
  exact (someLift_single depth _).symm

/-- The original independent actuality consumer receives the complete stored terminal value. -/
theorem stored_consumes_original_disposition (depth : Nat) :
    (∃ reached : ReachedAt (actor depth).rooted.rootSource.source,
      storedFinal depth = Finsupp.single
        (some (⟨(Registered.runtime depth).emittedOccurrence,.completed (.inl reached)⟩ : Registered.Point depth)) 1 ∧
      ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .settlement generated) ∨
    (∃ exhausted : ExhaustedAt (actor depth).rooted.rootSource.source,
      storedFinal depth = Finsupp.single
        (some (⟨(Registered.runtime depth).emittedOccurrence,.completed (.inr exhausted)⟩ : Registered.Point depth)) 1 ∧
      ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .obstruction generated) := by
  rcases Registered.consumes_original_disposition depth with
    ⟨reached, value, settlement, paid⟩ | ⟨exhausted, value, obstruction, paid⟩
  · exact Or.inl ⟨reached, (stored_final_value depth).trans ((congrArg (someLift depth) value).trans
      (someLift_single depth _)), settlement,paid⟩
  · exact Or.inr ⟨exhausted, (stored_final_value depth).trans ((congrArg (someLift depth) value).trans
      (someLift_single depth _)), obstruction,paid⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
