import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Runtime

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observation

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (first second : Cursor code) (matched : Aligned first second)
  (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code)

include matched in
private theorem depth_eq : depth first = depth second := by
  dsimp only [depth]
  rw [matched.history,matched.cut]

include matched in
theorem every_new_raw_occurrence_is_the_same (offset : Nat) :
    let left := (first.target rule rival).actualExecution (depth first+offset)
    let right := (second.target rule rival).actualExecution (depth second+offset)
    left.before = right.before ∧ left.submitted = right.submitted := by
  have inputs := (matched.after rule rival).input
  change (first.target rule rival).input = (second.target rule rival).input at inputs
  have indices := depth_eq first second matched
  dsimp only
  constructor <;> (unfold Machine.actualExecution; rw [inputs,indices])

include matched in
theorem aligned_legality : Window.legal first rule rival = Window.legal second rule rival := by
  unfold Window.legal
  rw [matched.horizon]
  apply List.all_congr rfl
  intro offset
  have raw := every_new_raw_occurrence_is_the_same first second matched rule rival offset
  dsimp only
  rw [raw.1,raw.2]

include matched in
theorem aligned_complete_execution :
    Aligned (Window.Runtime.execute first rule rival) (Window.Runtime.execute second rule rival) := by
  refine ⟨matched.history,?_,matched.owner,matched.budget,matched.after_body rule rival,?_⟩
  · change first.cut+Cut.horizon first.source first.entry first.cut =
      second.cut+Cut.horizon second.source second.entry second.cut
    rw [matched.horizon,matched.cut]
  · change (first.target rule rival).feedbackState (first.targetInput rule rival)
        (first.cut+Cut.horizon first.source first.entry first.cut) =
      (second.target rule rival).feedbackState (second.targetInput rule rival)
        (second.cut+Cut.horizon second.source second.entry second.cut)
    rw [←matched.horizon]
    exact matched.after_states rule rival _

theorem finite_complete_execution (point : Cursor code)
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule code) (against : Opponent code) :
    Aligned (Window.Runtime.execute point protocol (finiteRival point against))
      (Window.Runtime.execute point protocol against) :=
  ⟨rfl,rfl,rfl,rfl,Transport.the_original_finite_table_preserves_the_complete_emitter point protocol against,
    one_original_external_table_preserves_every_actual_ordinal_state point protocol against _⟩

def afterWindow (view : View (code := code)) (protocol : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (against : Opponent code) : View (code := code) :=
  ⟨Window.Runtime.execute view.point protocol against,⟨view.origin.val,by
    have earlier := view.origin.isLt
    change view.origin.val < view.point.source.history.length+2+
      (view.point.cut+Cut.horizon view.point.source view.point.entry view.point.cut)+1
    change view.origin.val < view.point.source.history.length+2+view.point.cut+1 at earlier
    omega⟩⟩

private theorem quiet_window (quiet : PublicDomain.quiet (code := code) = true)
    (view : View (code := code)) (protocol : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (against : Opponent code) : afterWindow view protocol against = afterWindow view protocol PublicDomain.silent := by
  have same := PublicDomain.quiet_controllers_are_identical quiet view.point protocol against
  unfold afterWindow Window.Runtime.execute Cursor.target Cursor.targetInput
  rw [same]

def nextWindow (protocol : Distributed.Recall.Information.Agency.Protocol.Rule code) (views : List (View (code := code))) :=
  if PublicDomain.quiet (code := code) then views.map (fun view => afterWindow view protocol PublicDomain.silent)
  else views.flatMap fun view => (Cut.tables view.point.source view.point.entry view.point.cut).map
    (fun table => afterWindow view protocol (Cut.opponent view.point.source view.point.entry view.point.cut table))

theorem the_complete_public_successor_retains_every_actual_debt_origin
    (views : List (View (code := code))) (actual : View (code := code))
    (covered : Knowledge.Contains views actual) (protocol : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (against : Opponent code) :
    Knowledge.Contains (nextWindow protocol views) (afterWindow actual protocol against) := by
  obtain ⟨representative,inside,matched⟩ := covered
  unfold nextWindow
  split
  · rename_i quiet
    refine ⟨afterWindow representative protocol PublicDomain.silent,List.mem_map.mpr ⟨representative,inside,rfl⟩,?_,matched.origin⟩
    rw [←quiet_window quiet representative protocol against]
    exact aligned_complete_execution representative.point actual.point matched.cursor protocol against
  · refine ⟨afterWindow representative protocol (finiteRival representative.point against),
      List.mem_flatMap.mpr ⟨representative,inside,List.mem_map.mpr
        ⟨externalTable representative.point against,Residual.restriction_is_generated _ _ _ against,rfl⟩⟩,
      (finite_complete_execution representative.point protocol against).trans
        (aligned_complete_execution representative.point actual.point matched.cursor protocol against),matched.origin⟩

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (representative actual : Cursor model.source.code) (same : Aligned representative actual)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (against : Opponent model.source.code)

include same in
theorem aligned_evaluation : Window.evaluate model representative protocol against =
    Window.evaluate model actual protocol against := by
  unfold Window.evaluate
  rw [Acceptance.aligned_evaluation model representative actual same protocol against,
    aligned_legality representative actual same protocol against]

include same in
theorem aligned_acceptance (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    Synthesis.accepts model.source.code (economicAxes representative.source representative.cut)
      (Window.evaluate model representative protocol against) (Window.evaluate model representative reference against) ↔
    Synthesis.accepts model.source.code (economicAxes actual.source actual.cut)
      (Window.evaluate model actual protocol against) (Window.evaluate model actual reference against) := by
  rw [Acceptance.aligned_economic_axes model representative actual same,
    aligned_evaluation model representative actual same protocol against,
    aligned_evaluation model representative actual same reference against]

theorem public_domain_acceptance_protects_the_actual_source
    (domain : List (Cursor model.source.code)) (covered : Continuation.Covered domain actual)
    (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (accepted : Search.acceptable model domain reference protocol) :
    Synthesis.accepts model.source.code (economicAxes actual.source actual.cut)
      (Window.evaluate model actual protocol against) (Window.evaluate model actual reference against) := by
  obtain ⟨representative,inside,matched⟩ := covered
  exact (aligned_acceptance model representative actual matched protocol against reference).mp
    ((Search.acceptable_iff_every_common_external_opponent model domain reference protocol).mp
      accepted ⟨representative,inside⟩ against)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observation
