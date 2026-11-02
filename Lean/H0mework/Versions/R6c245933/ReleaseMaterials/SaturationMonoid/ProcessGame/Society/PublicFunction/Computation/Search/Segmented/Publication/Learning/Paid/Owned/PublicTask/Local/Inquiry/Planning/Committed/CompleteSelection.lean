import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (cache : Inquiry.Frame task)

abbrev width := max (horizon task.domain-cache.past.length) (horizon (Planning.domain task cache))
abbrev localPlan (tail : Complete.FiniteProgram task.model.source.code) :=
  Continuation.Whole.Complete.clip (horizon (Planning.domain task cache)) tail.2
abbrev wholePlan (tail : Complete.FiniteProgram task.model.source.code) := Committed.proposal task cache tail

def normalise (tail : Complete.FiniteProgram task.model.source.code) : Program task.model.source.code (width task cache) :=
  ⟨(List.range (width task cache)).map (fun ordinal => tail.2.at task.original ordinal),by simp⟩

theorem normalise_stage (tail : Complete.FiniteProgram task.model.source.code)
    (ordinal : Nat) (inside : ordinal < width task cache) :
    (normalise task cache tail).at task.original ordinal = tail.2.at task.original ordinal := by
  simp only [Continuation.Whole.Program.at,normalise,List.getElem?_map]
  have element : (List.range (width task cache))[ordinal]? = some ordinal := List.getElem?_range inside
  rw [element]
  rfl

private theorem proposed_prefix (tail : Complete.FiniteProgram task.model.source.code) :
    (wholePlan task cache tail).controls.take cache.past.length = cache.past :=
  Prefix.Padding.preserves_prefix task.original _ cache.past
    (Prefix.every_completion_preserves_the_committed_control_prefix _ _ _ cache.within)

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem full_programmes_ext
    {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}
    (original : Prefix.Rule code) (first second : Program code fuel)
    (left : first.controls.length = fuel) (right : second.controls.length = fuel)
    (stages : ∀ ordinal < fuel,first.at original ordinal = second.at original ordinal) : first = second := by
  apply (Continuation.Whole.Program.mk.injEq ..).mpr
  apply List.ext_getElem (left.trans right.symm)
  intro ordinal a b
  have same := stages ordinal (by omega)
  simpa only [Continuation.Whole.Program.at,List.getElem?_eq_getElem a,List.getElem?_eq_getElem b,Option.getD_some] using same

theorem normalise_preserves_the_whole_proposal (tail : Complete.FiniteProgram task.model.source.code) :
    wholePlan task cache ⟨_,normalise task cache tail⟩ = wholePlan task cache tail := by
  apply full_programmes_ext task.original _ _ (Prefix.Commitment.padded_length _ _) (Prefix.Commitment.padded_length _ _)
  intro ordinal inside
  by_cases earlier : ordinal < cache.past.length
  · have first := Prefix.Commitment.retained_stages task.original _ cache.past
      (proposed_prefix task cache ⟨_,normalise task cache tail⟩) ordinal earlier
    have second := Prefix.Commitment.retained_stages task.original _ cache.past
      (proposed_prefix task cache tail) ordinal earlier
    exact first.symm.trans second
  · have offset : cache.past.length+(ordinal-cache.past.length) = ordinal := by omega
    rw [←offset,
      Committed.every_remaining_proposed_stage_is_the_submitted_stage task cache ⟨_,normalise task cache tail⟩ _ (by omega),
      Committed.every_remaining_proposed_stage_is_the_submitted_stage task cache tail _ (by omega)]
    exact normalise_stage task cache tail _ (lt_of_lt_of_le (by omega) (Nat.le_max_left _ _))

theorem normalise_preserves_every_local_evaluation (tail : Complete.FiniteProgram task.model.source.code)
    (world : Replanning.Point task.model (Planning.domain task cache))
    (rival : Opponent task.model.source.code) :
    actualEvaluation task.model world.val task.original (localPlan task cache ⟨_,normalise task cache tail⟩) rival =
      actualEvaluation task.model world.val task.original (localPlan task cache tail) rival := by
  apply stages_generate_the_same_complete_evaluation
  intro ordinal inside
  have localInside := lt_of_lt_of_le inside
    (Continuation.Whole.Complete.each_remaining_horizon_is_generated _ _ world.property)
  rw [Continuation.Whole.Complete.clipping_keeps_each_consumed_stage _ _ _ _ localInside,
    Continuation.Whole.Complete.clipping_keeps_each_consumed_stage _ _ _ _ localInside]
  exact normalise_stage task cache tail _ (lt_of_lt_of_le localInside (Nat.le_max_right _ _))

def admissible (tail : Complete.FiniteProgram task.model.source.code) : Prop :=
  Selection.acceptable task.model (Planning.domain task cache) task.original (Planning.reference task cache) (localPlan task cache tail) ∧
  Selection.acceptable task.model task.domain task.original cache.programme (wholePlan task cache tail)
instance (tail : Complete.FiniteProgram task.model.source.code) : Decidable (admissible task cache tail) := by
  unfold admissible
  infer_instance

theorem normalise_preserves_admissibility (tail : Complete.FiniteProgram task.model.source.code) :
    admissible task cache ⟨_,normalise task cache tail⟩ ↔ admissible task cache tail := by
  unfold admissible
  rw [normalise_preserves_the_whole_proposal]
  apply and_congr_left'
  rw [Selection.acceptable_iff_every_common_external_opponent,
    Selection.acceptable_iff_every_common_external_opponent]
  simp only [normalise_preserves_every_local_evaluation]

inductive Rejection (tail : Complete.FiniteProgram task.model.source.code) where
  | posterior (row : Selection.Rejection task.model (Planning.domain task cache) task.original
      (Planning.reference task cache) (localPlan task cache tail))
  | original (row : Selection.Rejection task.model task.domain task.original cache.programme (wholePlan task cache tail))

def inspect (tail : Complete.FiniteProgram task.model.source.code) : Sum (Rejection task cache tail) {_valid : Unit // admissible task cache tail} :=
  match Focused.Sparse.Decision.inspect task.model (Planning.domain task cache) task.original
      (Planning.reference task cache) (localPlan task cache tail) with
  | .rejected row generated broken => .inl (.posterior ⟨row,generated,broken⟩)
  | .accepted localAccepted =>
      match Focused.Sparse.Decision.inspect task.model task.domain task.original cache.programme (wholePlan task cache tail) with
      | .rejected row generated broken => .inl (.original ⟨row,generated,broken⟩)
      | .accepted globalAccepted => .inr ⟨(),localAccepted,globalAccepted⟩

structure Candidate where
  tail : Program task.model.source.code (width task cache)
  accepted : admissible task cache ⟨_,tail⟩
abbrev Candidate.protocol (candidate : Candidate task cache) := wholePlan task cache ⟨_,candidate.tail⟩

def check (tail : Program task.model.source.code (width task cache)) : Option (Candidate task cache) :=
  if valid : admissible task cache ⟨_,tail⟩ then some ⟨tail,valid⟩ else none

def candidates := (programs task.model.source.code (width task cache)).filterMap (check task cache)

theorem every_admissible_finite_tail_is_generated (tail : Complete.FiniteProgram task.model.source.code)
    (valid : admissible task cache tail) :
    ∃ candidate ∈ candidates task cache,candidate.protocol = wholePlan task cache tail := by
  have normal := (normalise_preserves_admissibility task cache tail).mpr valid
  refine ⟨⟨normalise task cache tail,normal⟩,List.mem_filterMap.mpr
    ⟨normalise task cache tail,every_bounded_program_is_source_generated _ _ _,?_⟩,
    normalise_preserves_the_whole_proposal task cache tail⟩
  simp only [check,dif_pos normal]

def comparisonCandidate (candidate : Candidate task cache) : Selection.Candidate task.model task.domain task.original cache.programme :=
  ⟨candidate.protocol,candidate.accepted.2⟩

local instance : DecidableEq (Prefix.Rule task.model.source.code) := Inquiry.ruleDecidableEq task
local instance : DecidableEq (Program task.model.source.code (horizon task.domain)) := fun first second =>
  decidable_of_iff (first.controls = second.controls) (by
    constructor
    · exact fun same => (Continuation.Whole.Program.mk.injEq ..).mpr same
    · exact fun same => congrArg (fun programme => programme.controls) same)

def recover (pool : List (Candidate task cache)) (chosen : Selection.Candidate task.model task.domain task.original cache.programme)
    (member : chosen ∈ pool.map (comparisonCandidate task cache)) :
    {candidate : Candidate task cache // candidate ∈ pool ∧ candidate.protocol = chosen.protocol} :=
  match found : pool.find? (fun candidate => decide (candidate.protocol = chosen.protocol)) with
  | some candidate => ⟨candidate,List.mem_of_find?_eq_some found,of_decide_eq_true (List.find?_some (p := fun candidate : Candidate task cache => decide (candidate.protocol = chosen.protocol)) found)⟩
  | none => False.elim (by
      obtain ⟨candidate,inside,same⟩ := List.mem_map.mp member
      have protocols := congrArg (fun item : Selection.Candidate task.model task.domain task.original cache.programme => item.protocol) same
      exact (List.find?_eq_none.mp found candidate inside) (decide_eq_true protocols))

abbrev Choice := Selected (Selection.axes (fuel := horizon task.domain) task.model task.domain)
  (fun candidate : Candidate task cache => Selection.benefit task.model task.domain task.original candidate.protocol) (candidates task cache)

inductive Outcome where
  | selected (choice : Choice task cache)
  | blocked (rejected : ∀ tail : Complete.FiniteProgram task.model.source.code, Rejection task cache tail)

def compile : Outcome task cache :=
  let pool := candidates task cache
  match chosen : Review.choose task.model task.domain task.original cache.programme (pool.map (comparisonCandidate task cache)) with
  | some selected =>
      let found := recover task cache pool selected.policy selected.original
      .selected ⟨found.val,found.property.1,by
        intro other inside strict
        apply selected.maximal (comparisonCandidate task cache other) (List.mem_map.mpr ⟨other,inside,rfl⟩)
        change Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
          (Selection.benefit task.model task.domain task.original) selected.policy.protocol other.protocol
        rw [←found.property.2]
        exact strict⟩
  | none => .blocked (fun tail => match inspect task cache tail with
      | .inl rejected => rejected
      | .inr valid => False.elim (by
          obtain ⟨candidate,inside,_⟩ := every_admissible_finite_tail_is_generated task cache tail valid.property
          have present : comparisonCandidate task cache candidate ∈ pool.map (comparisonCandidate task cache) := List.mem_map.mpr ⟨candidate,inside,rfl⟩
          rw [Review.choose_none_iff_empty] at chosen
          rw [chosen] at present
          exact List.not_mem_nil present))

theorem selected_has_no_admissible_finite_dominator (choice : Choice task cache)
    (tail : Complete.FiniteProgram task.model.source.code) (valid : admissible task cache tail) :
    ¬ Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
      (Selection.benefit task.model task.domain task.original) choice.policy.protocol (wholePlan task cache tail) := by
  obtain ⟨candidate,inside,same⟩ := every_admissible_finite_tail_is_generated task cache tail valid
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
    (Selection.benefit task.model task.domain task.original) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_available_admissible_strict_improvement_is_selected (choice : Choice task cache)
    (available : ∃ tail : Complete.FiniteProgram task.model.source.code,admissible task cache tail ∧
      Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
        (Selection.benefit task.model task.domain task.original) cache.programme (wholePlan task cache tail)) :
    Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
      (Selection.benefit task.model task.domain task.original) cache.programme choice.policy.protocol := by
  refine ⟨Selection.acceptance_bounds_every_benefit task.model task.domain task.original _ _ choice.policy.accepted.2,?_⟩
  intro reverse
  obtain ⟨tail,valid,better⟩ := available
  apply selected_has_no_admissible_finite_dominator task cache choice tail valid
  exact ⟨Distributed.noWorse_trans better.1 reverse,fun back => better.2 (Distributed.noWorse_trans reverse back)⟩

/-- Recompute both original relations and all finite alternatives; no maximality
proof or solver-selected comparison vector is an input to this checker. -/
def verify (tail : Complete.FiniteProgram task.model.source.code) : Bool :=
  decide (admissible task cache tail ∧ ∀ other ∈ programs task.model.source.code (width task cache),
    admissible task cache ⟨_,other⟩ →
      ¬ Review.improves task.model task.domain task.original (wholePlan task cache tail) (wholePlan task cache ⟨_,other⟩))

theorem verify_iff_every_admissible_finite_tail (tail : Complete.FiniteProgram task.model.source.code) :
    verify task cache tail = true ↔ admissible task cache tail ∧
      ∀ other : Complete.FiniteProgram task.model.source.code,admissible task cache other →
        ¬ Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
          (Selection.benefit task.model task.domain task.original) (wholePlan task cache tail) (wholePlan task cache other) := by
  simp only [verify,decide_eq_true_eq,Review.improves_iff]
  constructor
  · rintro ⟨valid,all⟩
    refine ⟨valid,fun other accepted => ?_⟩
    have checked := all (normalise task cache other) (every_bounded_program_is_source_generated _ _ _)
      ((normalise_preserves_admissibility task cache other).mpr accepted)
    rw [normalise_preserves_the_whole_proposal] at checked
    exact checked
  · rintro ⟨valid,all⟩
    exact ⟨valid,fun other _ accepted => all ⟨_,other⟩ accepted⟩

theorem every_generated_choice_passes_the_independent_checker (choice : Choice task cache) :
    verify task cache ⟨_,choice.policy.tail⟩ = true :=
  (verify_iff_every_admissible_finite_tail task cache _).mpr
    ⟨choice.policy.accepted,selected_has_no_admissible_finite_dominator task cache choice⟩

def rejectedRowFails (tail : Complete.FiniteProgram task.model.source.code) : Rejection task cache tail → Bool
  | .posterior row => !decide (Selection.holds task.model (Planning.domain task cache) task.original
      (Planning.reference task cache) (localPlan task cache tail) row.row)
  | .original row => !decide (Selection.holds task.model task.domain task.original cache.programme (wholePlan task cache tail) row.row)

theorem every_rejection_replays_its_own_original_row (tail : Complete.FiniteProgram task.model.source.code)
    (rejected : Rejection task cache tail) : rejectedRowFails task cache tail rejected = true := by
  cases rejected with
  | posterior row =>
      simp only [rejectedRowFails,decide_eq_false row.broken]
      rfl
  | original row =>
      simp only [rejectedRowFails,decide_eq_false row.broken]
      rfl

def review (outcome : Outcome task cache) : Bool := match outcome with
  | .selected choice => verify task cache ⟨_,choice.policy.tail⟩
  | .blocked rejected => (programs task.model.source.code (width task cache)).all fun tail =>
      rejectedRowFails task cache ⟨_,tail⟩ (rejected ⟨_,tail⟩)

theorem every_complete_output_passes_independent_replay (outcome : Outcome task cache) : review task cache outcome = true := by
  cases outcome with
  | selected choice => exact every_generated_choice_passes_the_independent_checker task cache choice
  | blocked rejected =>
      apply List.all_eq_true.mpr
      intro tail _
      exact every_rejection_replays_its_own_original_row task cache ⟨_,tail⟩ (rejected ⟨_,tail⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection
