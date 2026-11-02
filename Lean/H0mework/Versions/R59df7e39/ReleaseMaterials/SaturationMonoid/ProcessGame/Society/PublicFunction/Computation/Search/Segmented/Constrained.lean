import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Work

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Constrained
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (past : List (Distributed.Recall.Information.Agency.Protocol.Rule model.source.code))
  (reference : Program model.source.code (horizon domain))

abbrev Candidate := Prefix.Candidate model domain original past reference
abbrev Choice := Prefix.Choice model domain original past reference
variable (eligible : Candidate model domain original past reference → Bool)
  (work : Work model domain original past reference) (complete : work.todo = [])

abbrev maximal (candidate : Candidate model domain original past reference) (other : Candidate model domain original past reference) : Prop :=
  ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
    (fun proposal : Candidate model domain original past reference => Selection.benefit model domain original proposal.protocol)
    candidate other

def inspect (candidate : Candidate model domain original past reference) :=
  Distributed.inspect (maximal model domain original past reference candidate)
    (pool model domain original past reference work)

/-- Eligibility never shrinks the comparison pool. A returned choice is maximal
against every original accepted candidate, including ineligible alternatives. -/
def admit (candidate : {proposal // proposal ∈ pool model domain original past reference work}) :
    Option {choice : Choice model domain original past reference // eligible choice.policy = true} :=
  if suitable : eligible candidate.val = true then
    match inspect model domain original past reference work candidate.val with
    | .rejected .. => none
    | .accepted checked => some ⟨⟨candidate.val,
        (a_complete_cache_contains_exactly_all_accepted_candidates model domain original past reference work complete _).mp candidate.property,
        fun other inside => checked other
          ((a_complete_cache_contains_exactly_all_accepted_candidates model domain original past reference work complete _).mpr inside)⟩,suitable⟩
  else none

def choices := (pool model domain original past reference work).attach.filterMap
  (admit model domain original past reference eligible work complete)

def choose := (choices model domain original past reference eligible work complete).head?

theorem every_eligible_global_choice_is_generated
    (choice : Choice model domain original past reference) (suitable : eligible choice.policy = true) :
    (⟨choice,suitable⟩ : {choice : Choice model domain original past reference // eligible choice.policy = true}) ∈
      choices model domain original past reference eligible work complete := by
  have member : choice.policy ∈ pool model domain original past reference work :=
    (a_complete_cache_contains_exactly_all_accepted_candidates model domain original past reference work complete _).mpr choice.original
  apply List.mem_filterMap.mpr
  refine ⟨⟨choice.policy,member⟩,List.mem_attach _ _,?_⟩
  unfold admit
  rw [dif_pos suitable]
  cases inspected : inspect model domain original past reference work choice.policy with
  | rejected other included broken =>
      exact False.elim (broken (choice.maximal other
        ((a_complete_cache_contains_exactly_all_accepted_candidates model domain original past reference work complete _).mp included)))
  | accepted checked => rfl

theorem absence_rejects_every_eligible_global_choice
    (absent : choose model domain original past reference eligible work complete = none)
    (choice : Choice model domain original past reference) : eligible choice.policy ≠ true := by
  intro suitable
  have member := every_eligible_global_choice_is_generated model domain original past reference eligible work complete choice suitable
  have empty := List.head?_eq_none_iff.mp absent
  rw [empty] at member
  cases member

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Constrained
