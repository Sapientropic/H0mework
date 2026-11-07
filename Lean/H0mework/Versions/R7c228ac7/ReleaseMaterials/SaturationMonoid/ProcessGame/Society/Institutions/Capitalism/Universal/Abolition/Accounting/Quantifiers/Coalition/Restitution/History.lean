import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Allocation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

open Source.Program Innovation

noncomputable section

attribute [local irreducible] Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

def afterWords (current : Joint.Current seed claim)
    (words : List (RawEvent Party Good Port Technology Instrument)) : Joint.Current seed claim :=
  words.foldl (Joint.Current.advance seed claim) current

/-- A sum of each actual word's allocated return. This is a restriction of
the execution history; no receipt inventory or additional ledger is created. -/
def actualReturns : Joint.Current seed claim → List (RawEvent Party Good Port Technology Instrument) →
    Profit.Vector (Party := Party) (Good := Good)
  | _, [] => 0
  | current, word :: rest => returned seed claim current word +
      actualReturns (Joint.Current.advance seed claim current word) rest

theorem every_actual_prefix_conserves_allocated_returns_and_original_liability
    (current : Joint.Current seed claim) (words : List (RawEvent Party Good Port Technology Instrument)) :
    position (Entitlement.Duty.scope (Joint.window seed)) current.gross + actualReturns seed claim current words +
      liability seed claim (afterWords seed claim current words) = 0 := by
  induction words generalizing current with
  | nil => simp [actualReturns,afterWords,liability]
  | cons word rest inherited =>
      have first := actual_return_and_next_liability_preserve_the_whole_original_position seed claim current word
      have later := inherited (Joint.Current.advance seed claim current word)
      unfold liability at first
      change position (Entitlement.Duty.scope (Joint.window seed)) current.gross +
        (returned seed claim current word + actualReturns seed claim
          (Joint.Current.advance seed claim current word) rest) +
        liability seed claim (afterWords seed claim (Joint.Current.advance seed claim current word) rest) = 0
      calc
        _ = (position (Entitlement.Duty.scope (Joint.window seed)) current.gross + returned seed claim current word -
            position (Entitlement.Duty.scope (Joint.window seed)) (Joint.Current.advance seed claim current word).gross) +
          (position (Entitlement.Duty.scope (Joint.window seed)) (Joint.Current.advance seed claim current word).gross +
            actualReturns seed claim (Joint.Current.advance seed claim current word) rest +
            liability seed claim (afterWords seed claim (Joint.Current.advance seed claim current word) rest)) := by abel
        _ = 0 := by rw [sub_eq_add_neg,first,later,zero_add]

theorem no_coalition_keeps_source_control_income_after_original_liabilities
    (words : List (RawEvent Party Good Port Technology Instrument)) (members : Party → Bool) (good : Good) :
    let original := Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)
    read members good (originalControl (Joint.window seed) + actualReturns seed claim original words +
      liability seed claim (afterWords seed claim original words)) = 0 := by
  dsimp only
  rw [every_source_control_leg_is_counted_once_in_the_original_matrix]
  have balanced := every_actual_prefix_conserves_allocated_returns_and_original_liability seed claim
    (Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)) words
  have sourced : (Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)).gross =
      Entitlement.Duty.quantity (Joint.window seed) := rfl
  rw [sourced] at balanced
  simpa only [map_zero] using congrArg (read members good) balanced

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution
