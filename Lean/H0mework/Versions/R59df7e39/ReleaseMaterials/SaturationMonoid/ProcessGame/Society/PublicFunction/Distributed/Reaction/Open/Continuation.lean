import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- Local source laws, not an assumed continuation witness. -/
structure Stable (law : RawLaw Party Good Port Technology Instrument) : Prop where
  permissions : law.ReserveInsensitive
  duration : ∀ current reserve, law.duration (current.addReserve reserve) = law.duration current

variable (law : RawLaw Party Good Port Technology Instrument)

def Legal (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ item ∈ law.rawItems current word, law.Valid item.before item.request

instance (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Decidable (Legal law current word) := by
  unfold Legal
  infer_instance

omit [DecidableEq Port] [DecidableEq Technology] in
theorem next_addReserve (stable : Stable law) (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ party good, 0 ≤ reserve party good)
    (word : RawEvent Party Good Port Technology Instrument) (accepted : Legal law current word) :
    law.next (current.addReserve reserve) word = (law.next current word).addReserve reserve ∧
      Legal law (current.addReserve reserve) word := by
  have executed := law.execute_addReserve stable.permissions current reserve nonnegative 0 word accepted
  refine ⟨?_, executed.2⟩
  unfold RawLaw.next
  rw [executed.1, stable.duration]
  rfl

def LegalHistory (current : RawCurrent Party Good Technology Instrument) :
    List (RawEvent Party Good Port Technology Instrument) → Prop
  | [] => True
  | word :: tail => Legal law current word ∧ LegalHistory (law.next current word) tail

instance (current : RawCurrent Party Good Technology Instrument)
    (words : List (RawEvent Party Good Port Technology Instrument)) : Decidable (LegalHistory law current words) := by
  induction words generalizing current with
  | nil => exact isTrue True.intro
  | cons word tail ih =>
      dsimp only [LegalHistory]
      haveI := ih (law.next current word)
      infer_instance

/- No syntax bound is imposed on the old legal continuation. Every later
word starts at the preceding actual interpreted next, including its clock. -/
omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_old_legal_history_remains_open (stable : Stable law) (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ party good, 0 ≤ reserve party good)
    (words : List (RawEvent Party Good Port Technology Instrument)) (accepted : LegalHistory law current words) :
    LegalHistory law (current.addReserve reserve) words ∧
      words.foldl law.next (current.addReserve reserve) = (words.foldl law.next current).addReserve reserve := by
  induction words generalizing current with
  | nil => exact ⟨True.intro, rfl⟩
  | cons word tail ih =>
      have first := next_addReserve law stable current reserve nonnegative word accepted.1
      have rest := ih (law.next current word) accepted.2
      refine ⟨⟨first.2, ?_⟩, ?_⟩
      · simpa only [first.1] using rest.1
      · simpa only [List.foldl_cons, first.1] using rest.2

variable (code : Code Party Good Port Technology Instrument)

theorem selection_preserves_every_old_legal_history (stable : Stable code.law)
    (reference : code.Policy) (original : reference ∈ code.policies) (choice : Selection code reference)
    (opponent : Opponent code)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (admitted : history ∈ code.histories)
    (words : List (RawEvent Party Good Port Technology Instrument))
    (accepted : LegalHistory code.law (terminal code reference history opponent) words) :
    LegalHistory code.law (terminal code choice.policy.policy history opponent) words ∧
      words.foldl code.law.next (terminal code choice.policy.policy history opponent) =
        (words.foldl code.law.next (terminal code reference history opponent)).addReserve
          (reserve code choice.policy.policy reference history opponent) := by
  obtain ⟨nonnegative, same⟩ := generated_full_carrier_extension code _ _ choice.policy.generated original
    choice.policy.no_regression opponent history admitted
  rw [same]
  exact every_old_legal_history_remains_open code.law stable _ _ nonnegative words accepted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open
