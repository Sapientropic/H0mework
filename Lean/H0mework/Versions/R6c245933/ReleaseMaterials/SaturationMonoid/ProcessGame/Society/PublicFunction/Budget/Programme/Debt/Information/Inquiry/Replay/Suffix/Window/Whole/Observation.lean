import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Padding
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Acceptance
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}
def cover (programme : Program code fuel) : Program code (fuel+1) :=
  ⟨programme.controls,programme.bounded.trans (Nat.le_succ _)⟩
def controls (original : Prefix.Rule code) (programme : Program code fuel) := Prefix.Padding.controls original (cover programme)
omit [DecidableEq Port] [DecidableEq Technology] in
private theorem nonempty (original : Prefix.Rule code) (programme : Program code fuel) : controls original programme ≠ [] := by
  have size : (controls original programme).length = fuel+1 := Prefix.Padding.length original (cover programme)
  intro empty
  rw [empty] at size
  simp at size
private theorem same_source (point : Cursor code) (original : Prefix.Rule code) (programme : Program code fuel) (rival : Opponent code) :
    source point original (Splice.word (controls original programme)) rival = source point original programme rival :=
  Prefix.Padding.same_entire_source point original (cover programme) rival
theorem installs_aligned {first second : Cursor code} (matched : Aligned first second)
    (rival : Opponent code) (stages : List (Prefix.Rule code)) :
    Aligned (Splice.install first rival stages) (Splice.install second rival stages) := by
  induction stages generalizing first second with
  | nil => exact matched
  | cons head tail ih => exact ih (matched.after head rival)
theorem aligned_whole_bodies {first second : Cursor code} (matched : Aligned first second)
    (original : Prefix.Rule code) (programme : Program code fuel) (rival : Opponent code) :
    (source first original programme rival).body = (source second original programme rival).body := by
  have left := (Splice.body_assembly first rival original (controls original programme) (nonempty original programme)).trans
    (congrArg Machine.body (same_source first original programme rival))
  have right := (Splice.body_assembly second rival original (controls original programme) (nonempty original programme)).trans
    (congrArg Machine.body (same_source second original programme rival))
  exact left.symm.trans ((installs_aligned matched rival (controls original programme)).body.trans right)
theorem aligned_whole_inputs {first second : Cursor code} (matched : Aligned first second)
    (original : Prefix.Rule code) (programme : Program code fuel) (rival : Opponent code) :
    (source first original programme rival).input = (source second original programme rival).input := by
  have bodies := aligned_whole_bodies matched original programme rival
  have reports : (source first original programme rival).report = (source second original programme rival).report := by
    funext current
    exact congrArg (ProgrammeSource.ProgrammeReport.original current) (congrFun bodies current)
  simp only [Machine.input,bodies,reports]

theorem aligned_whole_states {first second : Cursor code} (matched : Aligned first second)
    (original : Prefix.Rule code) (programme : Program code fuel) (rival : Opponent code) (n : Nat) :
    Residual.run code (Residual.scheduleAt first.source first.cut (schedule first original programme).val)
      ⟨controller first original programme rival,first.entry.budget⟩ (Residual.seed first.source first.entry first.cut) n =
    Residual.run code (Residual.scheduleAt second.source second.cut (schedule second original programme).val)
      ⟨controller second original programme rival,second.entry.budget⟩ (Residual.seed second.source second.entry second.cut) n := by
  have inputs : (⟨controller first original programme rival,first.entry.budget⟩ : Input code) =
      ⟨controller second original programme rival,second.entry.budget⟩ := by
    have drivers : controller first original programme rival = controller second original programme rival := by
      funext history past frame
      change Distributed.Recall.Information.Agency.Protocol.driver code first.ownerStart (programme.at original (history.length-(first.history.length+1+first.cut))) rival history past frame =
        Distributed.Recall.Information.Agency.Protocol.driver code second.ownerStart (programme.at original (history.length-(second.history.length+1+second.cut))) rival history past frame
      rw [matched.owner,matched.history,matched.cut]
    exact congrArg₂ (fun opponent budget => (⟨opponent,budget⟩ : Input code)) drivers matched.budget
  induction n with
  | zero => exact matched.seed
  | succ n ih =>
    simp only [Residual.run] at ih ⊢
    rw [ih,inputs]
    let actual := Residual.run code
      (Residual.scheduleAt second.source second.cut (schedule second original programme).val)
      ⟨controller second original programme rival,second.entry.budget⟩ (Residual.seed second.source second.entry second.cut) n
    change Reaction.Feedback.advance code _ _ actual = Reaction.Feedback.advance code _ _ actual
    by_cases exhausted : actual.remaining = 0
    · cases (Residual.scheduleAt first.source first.cut (schedule first original programme).val n) <;>
        cases (Residual.scheduleAt second.source second.cut (schedule second original programme).val n) <;>
        simp only [Reaction.Feedback.advance,Reaction.Feedback.word,Reaction.Feedback.decision,exhausted,if_pos]
    · have remaining := Residual.remaining_is_the_seed_budget code
        (Residual.scheduleAt second.source second.cut (schedule second original programme).val)
        ⟨controller second original programme rival,second.entry.budget⟩ (Residual.seed second.source second.entry second.cut) n
      change actual.remaining = (Residual.seed second.source second.entry second.cut).remaining-n at remaining
      have inside : n < Cut.horizon second.source second.entry second.cut := by
        change n < (Residual.seed second.source second.entry second.cut).remaining
        omega
      have left : n < Cut.horizon first.source first.entry first.cut := by rw [matched.horizon];exact inside
      have firstPolicy : Residual.scheduleAt first.source first.cut (schedule first original programme).val n =
          some (programme.at original n).work.val := by
        simp only [Residual.scheduleAt,schedule,Continuation.Whole.schedule,List.getElem?_map,List.getElem?_range left,Option.map_some,Option.getD_some]
      have secondPolicy : Residual.scheduleAt second.source second.cut (schedule second original programme).val n =
          some (programme.at original n).work.val := by
        simp only [Residual.scheduleAt,schedule,Continuation.Whole.schedule,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]
      rw [firstPolicy,secondPolicy]

theorem every_new_whole_raw_occurrence_is_the_same {first second : Cursor code} (matched : Aligned first second)
    (original : Prefix.Rule code) (programme : Program code fuel) (rival : Opponent code) (offset : Nat) :
    let left := (source first original programme rival).actualExecution (depth first+offset)
    let right := (source second original programme rival).actualExecution (depth second+offset)
    left.before = right.before ∧ left.submitted = right.submitted := by
  have inputs := aligned_whole_inputs matched original programme rival
  have indices : depth first = depth second := by dsimp only [depth];rw [matched.history,matched.cut]
  constructor <;> (unfold Machine.actualExecution;rw [inputs,indices])

theorem aligned_whole_legality {first second : Cursor code} (matched : Aligned first second)
    (original : Prefix.Rule code) (programme : Program code fuel) (rival : Opponent code) :
    rawLegal first (controller first original programme rival) (schedule first original programme) =
      rawLegal second (controller second original programme rival) (schedule second original programme) := by
  unfold rawLegal
  rw [matched.horizon]
  apply List.all_congr rfl
  intro offset
  have raw := every_new_whole_raw_occurrence_is_the_same matched original programme rival offset
  dsimp only
  rw [raw.1,raw.2]

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (first second : Cursor model.source.code) (matched : Aligned first second)
  (original : Prefix.Rule model.source.code) (programme : Program model.source.code fuel)
  (rival : Opponent model.source.code)

include matched in
theorem aligned_whole_evaluation : actualEvaluation model first original programme rival =
    actualEvaluation model second original programme rival := by
  have evaluated := Acceptance.Generated.aligned_evaluation model first second matched
    (controller first original programme rival) (controller second original programme rival)
    (schedule first original programme) (schedule second original programme)
    (aligned_whole_inputs matched original programme rival) (aligned_whole_states matched original programme rival)
  apply (Evaluation.mk.injEq ..).mpr
  exact ⟨aligned_whole_legality matched original programme rival,
    congrArg Evaluation.complete evaluated,congrArg Evaluation.profile evaluated,
    congrArg Evaluation.native evaluated,congrArg Evaluation.value evaluated⟩

include matched in
theorem aligned_whole_acceptance (reference : Program model.source.code fuel) :
    Synthesis.accepts model.source.code (economicAxes first.source first.cut)
      (actualEvaluation model first original programme rival) (actualEvaluation model first original reference rival) ↔
    Synthesis.accepts model.source.code (economicAxes second.source second.cut)
      (actualEvaluation model second original programme rival) (actualEvaluation model second original reference rival) := by
  rw [Acceptance.aligned_economic_axes model first second matched,
    aligned_whole_evaluation model first second matched original programme rival,
    aligned_whole_evaluation model first second matched original reference rival]


include matched in
theorem aligned_complete_execution :
    Aligned (Whole.Runtime.execute first original programme rival)
      (Whole.Runtime.execute second original programme rival) := by
  refine ⟨matched.history,?_,matched.owner,matched.budget,
    aligned_whole_bodies matched original programme rival,?_⟩
  · change first.cut+Cut.horizon first.source first.entry first.cut =
      second.cut+Cut.horizon second.source second.entry second.cut
    rw [matched.horizon,matched.cut]
  · change (source first original programme rival).feedbackState (entry first original programme rival)
      (first.cut+Cut.horizon first.source first.entry first.cut) =
      (source second original programme rival).feedbackState (entry second original programme rival)
      (second.cut+Cut.horizon second.source second.entry second.cut)
    rw [Continuation.Whole.the_complete_program_runs_in_its_own_actual_source,
      Continuation.Whole.the_complete_program_runs_in_its_own_actual_source,←matched.horizon]
    exact aligned_whole_states matched original programme rival _

theorem public_domain_acceptance_protects_every_covered_actual_source
    (domain : List (Cursor model.source.code)) (covered : Continuation.Covered domain second)
    (reference : Program model.source.code fuel)
    (accepted : Selection.acceptable model domain original reference programme) :
    Synthesis.accepts model.source.code (economicAxes second.source second.cut)
      (actualEvaluation model second original programme rival) (actualEvaluation model second original reference rival) := by
  obtain ⟨representative,inside,matching⟩ := covered
  exact (aligned_whole_acceptance model representative second matching original programme rival reference).mp
    ((Selection.acceptable_iff_every_common_external_opponent model domain original reference programme).mp
      accepted ⟨representative,inside⟩ rival)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation
