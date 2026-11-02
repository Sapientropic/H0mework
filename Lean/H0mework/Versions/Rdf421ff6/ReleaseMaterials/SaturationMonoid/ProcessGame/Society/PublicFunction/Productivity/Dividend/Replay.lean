import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Replay

open Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication

abbrev Item := ExecutionItem Bool Bool (Option Bool) Bool Unit

def retime (clock : ℚ) (round : Nat) (item : Item) : Item :=
  { item with before := item.before.retime clock round }

theorem items (n : Nat) (current : Current) (clock : ℚ) (round index : Nat)
    (word : List RequestAt) :
    ((law n).execute (current.retime clock round) index word).items =
      (((law n).execute current index word).items.map (retime clock round)) := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail ih =>
    simp only [RawLaw.execute, (law n).step_retime (time_independent n), ih, List.map_cons]
    rfl

theorem debit (n : Nat) (current : Current) (clock : ℚ) (round : Nat) (request : RequestAt) :
    (law n).actualDebit (current.retime clock round) request = (law n).actualDebit current request := by
  simp only [RawLaw.actualDebit, (law n).valid_retime (time_independent n)]
  split <;> rfl

theorem credit (n : Nat) (current : Current) (clock : ℚ) (round : Nat) (request : RequestAt) :
    (law n).actualCredit (current.retime clock round) request = (law n).actualCredit current request := by
  simp only [RawLaw.actualCredit, (law n).valid_retime (time_independent n)]
  split <;> rfl

theorem totalDebit (n : Nat) (current : Current) (clock : ℚ) (round index : Nat)
    (word : List RequestAt) (party good : Bool) :
    (law n).totalDebit ((law n).execute (current.retime clock round) index word).items party good =
      (law n).totalDebit ((law n).execute current index word).items party good := by
  rw [items]
  simp only [RawLaw.totalDebit, List.map_map, Function.comp_def, retime, debit]

theorem totalCredit (n : Nat) (current : Current) (clock : ℚ) (round index : Nat)
    (word : List RequestAt) (party good : Bool) :
    (law n).totalCredit ((law n).execute (current.retime clock round) index word).items party good =
      (law n).totalCredit ((law n).execute current index word).items party good := by
  rw [items]
  simp only [RawLaw.totalCredit, List.map_map, Function.comp_def, retime, credit]

theorem bundlePaid (n : Nat) (current : Current) (clock : ℚ) (round : Nat)
    (word : List RequestAt) (party : Bool) (goods : Bundle Bool) (purpose : Use)
    (paid : Exit.Necessity.BundlePaid (law n) current word party goods purpose) :
    Exit.Necessity.BundlePaid (law n) (current.retime clock round) word party goods purpose := by
  rcases paid with empty | ⟨item, inside, valid, matched⟩
  · exact Or.inl empty
  · refine Or.inr ⟨retime clock round item, ?_, ?_, matched⟩
    · rw [RawLaw.rawItems, items]
      exact List.mem_map.mpr ⟨item, inside, rfl⟩
    · exact ((law n).valid_retime (time_independent n) _ _ _ _).mpr valid

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Replay
