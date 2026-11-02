import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Selection

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (active : bound.source.feedback? = some input)
  (empty : bound.source.continuation = []) (cut : Nat)

def atCut : Disposition bound input cut active empty :=
  match (Runtime.facade bound input active empty).readoutAt
      (Runtime.activated bound input active empty (bound.source.history.length + 2 + cut)) .responsibilities with
  | .inl actual => actual.2 cut (by
      change (ProgrammeHistory.visitAt bound.source.input
        (Runtime.activated bound input active empty (bound.source.history.length + 2 + cut)).state).current = _
      exact congrArg (fun ordinal => (ProgrammeHistory.visitAt bound.source.input ordinal).current)
        (Runtime.activated_state_is_the_generated_ordinal bound input active empty _))
  | .inr impossible => nomatch impossible

variable (reference : Cut.Term bound.source input cut) (feasible : Cut.Feasible bound.source input cut reference)

def choice := Trace.Selection.choiceFrom bound input cut active reference
  ((atCut bound input active empty cut).selection reference).outcome feasible

def execution (rival : Opponent bound.source.code) : Future.Execution bound.source input cut rival
    (choice bound input active empty cut reference feasible).policy.term.val :=
  Trace.Selection.selectedExecution bound input cut active reference
    ((atCut bound input active empty cut).selection reference) feasible rival

def selected (rival : Opponent bound.source.code) :=
  candidate bound input cut rival (choice bound input active empty cut reference feasible).policy.term

abbrev selectedInput (rival : Opponent bound.source.code) := Future.takeover bound.source input cut rival

theorem selected_active (rival : Opponent bound.source.code) :
    (selected bound input active empty cut reference feasible rival).source.feedback? =
      some (selectedInput bound input cut rival) := rfl

include empty in
theorem selected_empty (rival : Opponent bound.source.code) :
    (selected bound input active empty cut reference feasible rival).source.continuation = [] := empty

/-- The next search reads the selected source after its first actual step, including its own
    observations, paid actions, native responsibilities and remaining budget. -/
def next (rival : Opponent bound.source.code) :=
  atCut (selected bound input active empty cut reference feasible rival) (selectedInput bound input cut rival)
    (selected_active bound input active empty cut reference feasible rival)
    (selected_empty bound input active empty cut reference feasible rival) (cut + 1)

theorem next_reads_the_actual_selected_residual (rival : Opponent bound.source.code) :
    (next bound input active empty cut reference feasible rival).feedback.state =
      Residual.run bound.source.code
        (Residual.scheduleAt bound.source cut (choice bound input active empty cut reference feasible).policy.term.val)
        ⟨rival, input.budget⟩ (Residual.seed bound.source input cut) 1 :=
  (next bound input active empty cut reference feasible rival).feedback.state_exact.trans
    ((execution bound input active empty cut reference feasible rival).complete_states 1)

theorem selected_and_next_are_consumed_by_their_own_roots (rival : Opponent bound.source.code) :
    let original := Runtime.activated bound input active empty (bound.source.history.length + 2 + cut)
    let target := selected bound input active empty cut reference feasible rival
    let targetInput := selectedInput bound input cut rival
    let targetActive := selected_active bound input active empty cut reference feasible rival
    let targetEmpty := selected_empty bound input active empty cut reference feasible rival
    let successor := Runtime.activated target targetInput targetActive targetEmpty (target.source.history.length + 2 + (cut + 1))
    Trace.Selection.AgainstEveryOpponent bound input cut active
        (choice bound input active empty cut reference feasible).policy.term reference ∧
      Trace.Selection.verify bound input cut active reference
        (choice bound input active empty cut reference feasible).policy.term = true ∧
      (next bound input active empty cut reference feasible rival).current =
        Native.Authority.fullGenerate target (target.source.history.length + 1 + (cut + 1)) ∧
      HEq original.tick.generated.wholeLedgerWriteBack
        (original.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt original.current.visit.current) ∧
      original.tick.nextCurrent = (Runtime.facade bound input active empty).process.stateAt
        ((Runtime.facade bound input active empty).process.successor original.state) ∧
      HEq successor.tick.generated.wholeLedgerWriteBack
        (successor.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt successor.current.visit.current) ∧
      successor.tick.nextCurrent = (Runtime.facade target targetInput targetActive targetEmpty).process.stateAt
        ((Runtime.facade target targetInput targetActive targetEmpty).process.successor successor.state) := by
  have original := (Runtime.facade bound input active empty).readoutAt_factorizes
    (Runtime.activated bound input active empty (bound.source.history.length + 2 + cut)) .responsibilities
  have successor := (Runtime.facade (selected bound input active empty cut reference feasible rival) (selectedInput bound input cut rival)
    (selected_active bound input active empty cut reference feasible rival) (selected_empty bound input active empty cut reference feasible rival)).readoutAt_factorizes
    (Runtime.activated (selected bound input active empty cut reference feasible rival) (selectedInput bound input cut rival)
      (selected_active bound input active empty cut reference feasible rival) (selected_empty bound input active empty cut reference feasible rival)
      ((selected bound input active empty cut reference feasible rival).source.history.length + 2 + (cut + 1))) .responsibilities
  exact ⟨(Trace.Selection.comparison_iff_every_future_opponent bound input cut active empty _ _).mp
      (choice bound input active empty cut reference feasible).policy.no_regression,
    Trace.Selection.independent_replay_accepts_selection bound input cut active reference _,
    (next bound input active empty cut reference feasible rival).current_exact,
    original.2.2.1, original.2.2.2.2, successor.2.2.1, successor.2.2.2.2⟩

def verifiedTarget (term : Cut.Term bound.source input cut)
    (verified : Trace.Selection.verify bound input cut active reference term = true) (rival : Opponent bound.source.code) :=
  candidate bound input cut rival (Trace.Selection.choiceOfVerified bound input cut active reference term verified).policy.term

def verifiedNext (term : Cut.Term bound.source input cut)
    (verified : Trace.Selection.verify bound input cut active reference term = true) (rival : Opponent bound.source.code) :=
  atCut (verifiedTarget bound input active cut reference term verified rival) (Future.takeover bound.source input cut rival)
    rfl empty (cut + 1)

theorem verified_next_reads_the_supplied_planners_actual_residual (term : Cut.Term bound.source input cut)
    (verified : Trace.Selection.verify bound input cut active reference term = true) (rival : Opponent bound.source.code) :
    (verifiedNext bound input active empty cut reference term verified rival).feedback.state =
      Residual.run bound.source.code (Residual.scheduleAt bound.source cut term.val)
        ⟨rival, input.budget⟩ (Residual.seed bound.source input cut) 1 :=
  (verifiedNext bound input active empty cut reference term verified rival).feedback.state_exact.trans
    ((((atCut bound input active empty cut).selection reference).verified_realization term verified rival).complete_states 1)

theorem every_verified_planner_owns_its_next_search_root (term : Cut.Term bound.source input cut)
    (verified : Trace.Selection.verify bound input cut active reference term = true) (rival : Opponent bound.source.code) :
    let target := verifiedTarget bound input active cut reference term verified rival
    let targetInput := Future.takeover bound.source input cut rival
    let actual := Runtime.activated target targetInput rfl empty (target.source.history.length + 2 + (cut + 1))
    (verifiedNext bound input active empty cut reference term verified rival).current =
        Native.Authority.fullGenerate target (target.source.history.length + 1 + (cut + 1)) ∧
      HEq ((Runtime.facade target targetInput rfl empty).readoutAt actual .responsibilities)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (Runtime.facade target targetInput rfl empty).process.stateAt
        ((Runtime.facade target targetInput rfl empty).process.successor actual.state) := by
  have rooted := (Runtime.facade (verifiedTarget bound input active cut reference term verified rival)
    (Future.takeover bound.source input cut rival) rfl empty).readoutAt_factorizes
    (Runtime.activated (verifiedTarget bound input active cut reference term verified rival)
      (Future.takeover bound.source input cut rival) rfl empty
      ((verifiedTarget bound input active cut reference term verified rival).source.history.length + 2 + (cut + 1))) .responsibilities
  exact ⟨(verifiedNext bound input active empty cut reference term verified rival).current_exact,
    rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Selection
