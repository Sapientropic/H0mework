import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Background

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program Innovation
open Evolution.Ingress.Joint Evolution.Ingress.Joint.Material

noncomputable section

attribute [local irreducible] Execution.Selected.items Joint.Planning.selected Joint.Planning.actualNext Joint.Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

/-- This mathematical observer reads only submitted prefixes; the input family is not a native payload. -/
def observedCurrent (submitted : Nat → Evolution.Sparse.History.Submission seed.claim) (n : Nat) :=
  Evolution.Sparse.History.run seed.claim (futureSource seed claim) ((List.range n).map submitted)

def observedHistory (submitted : Nat → Evolution.Sparse.History.Submission seed.claim) (n : Nat) :
    Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) (observedCurrent seed claim submitted n) :=
  Evolution.Sparse.History.generate seed.claim (futureSource seed claim) ((List.range n).map submitted)

theorem unsubmitted_future_inputs_do_not_change_the_actual_observed_current
    (left right : Nat → Evolution.Sparse.History.Submission seed.claim) (n : Nat)
    (same : ∀ i < n, left i = right i) :
    observedCurrent seed claim left n = observedCurrent seed claim right n := by
  apply congrArg (Evolution.Sparse.History.run seed.claim (futureSource seed claim))
  exact List.map_congr_left (fun i inside => same i (List.mem_range.mp inside))

theorem every_stage_of_every_open_mechanism_sequence_keeps_capital_excluded_and_every_coalition_accounted
    (enough : Joint.Planning.Enough seed claim (shared seed claim))
    (submitted : Nat → Evolution.Sparse.History.Submission seed.claim) (n : Nat)
    (members : Party → Bool) (good : Good) :
    Global.NoCapital (observedCurrent seed claim submitted n).actualLaw ∧
      Responsibility.Family.State.isPaid seed.claim
        (Evolution.Sparse.Current.state seed.claim (observedCurrent seed claim submitted n)) ∧
      Coalition.read members good (Coalition.Sparse.income seed.claim (observedHistory seed claim submitted n)) ≤ 0 ∧
      Coalition.read members good (Coalition.Sparse.income seed.claim (observedHistory seed claim submitted n)) +
        Coalition.read members good (Coalition.Sparse.consumed seed.claim (observedHistory seed claim submitted n)) = 0 :=
  every_coalition_has_its_full_account_through_every_actual_open_mechanism_history
    seed claim enough (observedHistory seed claim submitted n) members good

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
