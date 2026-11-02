import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWindowPlan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalRuleTable

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def admit (requests : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :=
  if requests ∈ words code.actions code.actionLimit then requests else []

theorem admitted_words_are_supported (requests : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    admit (code := code) requests ∈ words code.actions code.actionLimit := by
  dsimp only [admit]
  split
  · assumption
  · exact (mem_words_iff _ _ _).mpr (by simp)

-- Compare the complete raw policy and owned event table, not a successful run
-- or a masked action. This permits substitution before any world is executed.
def verify (candidate original : Rule code) : Bool := code.keys.attach.all fun key =>
  decide (candidate.work.val key.val key.property = original.work.val key.val key.property) &&
  decide ((candidate.events key.val key.property).val = (original.events key.val key.property).val)

theorem verified_table_is_the_entire_original_rule (candidate original : Rule code)
    (accepted : verify candidate original = true) : candidate = original := by
  have rows := List.all_eq_true.mp accepted
  have work : candidate.work = original.work := by
    apply Subtype.ext
    funext key inside
    have row := rows ⟨key, inside⟩ (List.mem_attach _ _)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at row
    exact row.1
  have events : candidate.events = original.events := by
    funext key inside
    apply Subtype.ext
    have row := rows ⟨key, inside⟩ (List.mem_attach _ _)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at row
    exact row.2
  cases candidate
  cases original
  cases work
  cases events
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalRuleTable
