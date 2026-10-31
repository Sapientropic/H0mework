import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Effects

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

open Institutions.Capitalism.Universal.Source.Program

theorem valid_debits_only_the_signer (current : Current) (request : RequestAt)
    (accepted : law.Valid current request) :
    ∀ entry ∈ law.debit current request, entry.1.1 = request.signer := by
  have policy := accepted.1.2
  have located (owner : Party) (goods : Bundle Good) (same : owner = request.signer) :
      ∀ entry ∈ locate owner goods, entry.1.1 = request.signer := by
    intro entry inside
    obtain ⟨item, _member, rfl⟩ := List.mem_map.mp inside
    exact same
  cases operation : request.operation <;>
    simp only [RawLaw.operationAllowed, law, RawPolicy.eval, operation, decide_eq_true_eq] at policy <;>
    simp only [RawLaw.debit, operation]
  all_goals first | exact located _ _ policy.1 | simp

def noSeedInitial : Current :=
  { initial with stock := fun actor good => if good = .seed then 0 else initial.stock actor good }

def noSeedSource : OutstandingSource Party Good Port Technology Unit :=
  { source with seed := {
      source.seed with
      initial := noSeedInitial
      refused := by
        let before := (law.execute (law.next noSeedInitial []) 0 (original.take 8)).final
        refine ⟨⟨8, before, production 0⟩, ?_, ?_⟩
        · change _ ∈ law.rawItems (law.next noSeedInitial []) original
          simp [before, original, RawLaw.rawItems, RawLaw.execute]
        · decide +kernel } }

theorem missing_physical_seed_is_not_compiled_away :
    (noSeedSource.currentAt 3).technology.1 = true ∧
    ¬ Ready (noSeedSource.currentAt 3) ∧
    (noSeedSource.actualExecution 2).submitted = [] ∧
    (noSeedSource.currentAt 4).claims () 0 2 = 1 ∧
    (noSeedSource.currentAt 4).stock 0 .feed = 24 ∧
    (noSeedSource.currentAt 4).stock 0 .seed = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(noSeedSource.canonical_frame 3).1]; decide +kernel
  · rw [(noSeedSource.canonical_frame 3).1]; decide +kernel
  · rw [noSeedSource.actual_execution_word]
    decide +kernel
  all_goals rw [(noSeedSource.canonical_frame 4).1]; decide +kernel

def allGoods : List Good := [.seed, .feed, .life, .spare, .waste, .energy, .labor]

def receiptStock (actor : Party) (good : Good) : ℚ :=
  initial.stock actor good - law.totalDebit migrationItems actor good + law.totalCredit migrationItems actor good

/-- A second consumer folds the original debit/credit receipts instead of
updating an inventory by the interpreter's sequential stock recurrence. -/
theorem receipt_fold_matches_actual_inventory :
    ∀ actor ∈ List.finRange 6, ∀ good ∈ allGoods,
      receiptStock actor good = (source.frameAt 11).raw.stock actor good := by
  decide +kernel

theorem every_actual_boundary_balances (ordinal : Nat) (actor : Party) (good : Good) :
    (source.frameAt (ordinal + 1)).raw.stock actor good +
      law.totalDebit (law.rawItems (source.frameAt ordinal).raw
        (source.frameWord ordinal (source.frameAt ordinal))) actor good =
      (source.frameAt ordinal).raw.stock actor good +
      law.totalCredit (law.rawItems (source.frameAt ordinal).raw
        (source.frameWord ordinal (source.frameAt ordinal))) actor good :=
  law.actual_next_material_balance _ _ actor good

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
