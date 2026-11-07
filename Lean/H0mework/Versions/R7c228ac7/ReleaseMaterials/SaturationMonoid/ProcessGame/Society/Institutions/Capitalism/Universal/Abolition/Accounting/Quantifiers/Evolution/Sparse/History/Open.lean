import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Mechanism.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.History

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)

attribute [local irreducible] Mechanism.next

structure Submission : Type where
  programme : Mechanism.Programme claim
  input : Request Party Good Port Technology Instrument

/-- Each submitted programme is new source code. Its successor is fixed by
the actual root action, including a refusal with real partial payment. -/
inductive Actual : Current (oldN := oldN) claim → Current (oldN := oldN) claim → Type 4
  | empty (current) : Actual current current
  | step (current) (programme : Mechanism.Programme claim) (input : Request Party Good Port Technology Instrument)
      {target} (later : Actual (Mechanism.next claim current programme input) target) : Actual current target

def run (current : Current (oldN := oldN) claim) : List (Submission claim) → Current (oldN := oldN) claim
  | [] => current
  | submitted :: later => run (Mechanism.next claim current submitted.programme submitted.input) later

def generate (current : Current (oldN := oldN) claim) (submitted : List (Submission claim)) :
    Actual claim current (run claim current submitted) := match submitted with
  | [] => .empty current
  | first :: later => .step current first.programme first.input
      (generate (Mechanism.next claim current first.programme first.input) later)

theorem every_history_keeps_all_original_financial_addresses
    {source target : Current (oldN := oldN) claim} (history : Actual claim source target) :
    (Current.state claim target).raw.claims = (Current.state claim source).raw.claims := by
  induction history with
  | empty => rfl
  | step current programme input later inherited =>
    exact inherited.trans (Mechanism.every_old_claim_is_preserved claim current programme input)

theorem every_history_keeps_the_same_effective_law_and_roster
    {source target : Current (oldN := oldN) claim} (history : Actual claim source target) :
    target.actualLaw = source.actualLaw ∧ target.members = source.members := by
  induction history with
  | empty => exact ⟨rfl,rfl⟩
  | step current programme input later inherited =>
    have same := Mechanism.the_same_effective_law_and_roster_are_preserved claim current programme input
    exact ⟨inherited.1.trans same.1,inherited.2.trans same.2⟩

theorem every_history_preserves_each_original_liability
    {source target : Current (oldN := oldN) claim} (history : Actual claim source target) (key : Party × Good) :
    (Current.state claim target).remaining key ≤ (Current.state claim source).remaining key := by
  induction history with
  | empty => exact le_rfl
  | step current programme input later inherited =>
    exact inherited.trans (Mechanism.no_original_cell_is_refilled claim current programme input key)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.History
