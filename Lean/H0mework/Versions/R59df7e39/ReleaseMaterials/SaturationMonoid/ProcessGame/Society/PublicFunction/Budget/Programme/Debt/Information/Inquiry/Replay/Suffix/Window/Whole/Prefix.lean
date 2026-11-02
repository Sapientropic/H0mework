import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Splice

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

abbrev Rule := @Distributed.Recall.Information.Agency.Protocol.Rule

def extension (bound : Nat) (past : List (Rule code)) (tail : Program code fuel) : Program code bound :=
  clip bound (Splice.word (past++tail.controls))

def extensions (bound : Nat) (past : List (Rule code)) : List (Program code bound) :=
  (programs code bound).map (extension bound past)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem tail_normalization_does_not_change_any_consumed_prefix_extension
    (bound : Nat) (past : List (Rule code)) (tail : Program code fuel) :
    extension bound past (clip bound tail) = extension bound past tail := by
  apply (Continuation.Whole.Program.mk.injEq ..).mpr
  change (past++tail.controls.take bound).take bound = (past++tail.controls).take bound
  rw [List.take_append,List.take_append,List.take_take,Nat.min_eq_left (Nat.sub_le _ _)]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_finite_tail_is_generated (bound : Nat) (past : List (Rule code))
    (tail : Program code fuel) : extension bound past tail ∈ extensions bound past := by
  refine List.mem_map.mpr ⟨clip bound tail,every_bounded_program_is_source_generated _ _ _,?_⟩
  exact tail_normalization_does_not_change_any_consumed_prefix_extension bound past tail

omit [DecidableEq Port] [DecidableEq Technology] in
theorem the_committed_plan_is_one_of_its_own_prefix_completions
    (bound : Nat) (committed : Program code fuel) (cut : Nat) :
    extension bound (committed.controls.take cut) (Splice.word (committed.controls.drop cut)) = clip bound committed := by
  unfold extension Splice.word
  rw [List.take_append_drop]
  rfl

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (past : List (Rule model.source.code)) (reference : Program model.source.code (horizon domain))

/-- A replacement planner submits only a future tail. The already published past
    is constructed by the host, never supplied by that proposal. -/
structure Candidate where
  tail : Program model.source.code (horizon domain)
  accepted : Selection.acceptable model domain original reference (extension (horizon domain) past tail)

abbrev Candidate.protocol (candidate : Candidate model domain original past reference) :=
  extension (horizon domain) past candidate.tail

def check (tail : Program model.source.code (horizon domain)) : Option (Candidate model domain original past reference) :=
  if accepted : Selection.acceptable model domain original reference (extension (horizon domain) past tail) then
    some ⟨tail,accepted⟩ else none

def candidates := (programs model.source.code (horizon domain)).filterMap (check model domain original past reference)

abbrev Choice := Selected (Selection.axes (fuel := horizon domain) model domain)
  (fun candidate : Candidate model domain original past reference => Selection.benefit model domain original candidate.protocol)
  (candidates model domain original past reference)

theorem every_accepted_completion_is_generated (tail : Complete.FiniteProgram model.source.code)
    (accepted : Selection.acceptable model domain original reference (extension (horizon domain) past tail.2)) :
    ∃ candidate ∈ candidates model domain original past reference,
      candidate.protocol = extension (horizon domain) past tail.2 := by
  have same := tail_normalization_does_not_change_any_consumed_prefix_extension (horizon domain) past tail.2
  have normalized : Selection.acceptable model domain original reference
      (extension (horizon domain) past (clip (horizon domain) tail.2)) := by rw [same];exact accepted
  refine ⟨⟨clip (horizon domain) tail.2,normalized⟩,List.mem_filterMap.mpr
    ⟨clip (horizon domain) tail.2,every_bounded_program_is_source_generated _ _ _,?_⟩,same⟩
  simp only [check,dif_pos normalized]

inductive Outcome where
  | selected (choice : Choice model domain original past reference)
  | blocked (rejected : ∀ tail : Complete.FiniteProgram model.source.code,
      Selection.Rejection model domain original reference (extension (horizon domain) past tail.2))

def compile : Outcome model domain original past reference :=
  match result : Distributed.choose (Selection.axes (fuel := horizon domain) model domain)
    (fun candidate : Candidate model domain original past reference => Selection.benefit model domain original candidate.protocol)
    (candidates model domain original past reference) with
  | some choice => .selected choice
  | none => .blocked (fun tail => match Distributed.inspect
      (Selection.holds model domain original reference (extension (horizon domain) past tail.2)) (Replanning.rows model domain) with
    | .rejected row generated broken => ⟨row,generated,broken⟩
    | .accepted accepted => False.elim (by
      obtain ⟨candidate,inside,_⟩ := every_accepted_completion_is_generated model domain original past reference tail accepted
      rw [choose_none_iff_empty] at result
      simp only [result,List.not_mem_nil] at inside))


theorem the_generated_choice_has_no_full_responsibility_completion_dominator
    (choice : Choice model domain original past reference)
    (tail : Complete.FiniteProgram model.source.code)
    (accepted : Selection.acceptable model domain original choice.policy.protocol
      (extension (horizon domain) past tail.2)) :
    ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
      (Selection.benefit model domain original) choice.policy.protocol (extension (horizon domain) past tail.2) := by
  have through := Selection.acceptable_trans model domain original _ _ _ accepted choice.policy.accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_completion_is_generated model domain original past reference tail through
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
    (Selection.benefit model domain original) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal

theorem every_available_full_responsibility_completion_improvement_is_realized
    (choice : Choice model domain original past reference)
    (available : ∃ tail : Complete.FiniteProgram model.source.code,
      Selection.acceptable model domain original reference (extension (horizon domain) past tail.2) ∧
      Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
        (Selection.benefit model domain original) reference (extension (horizon domain) past tail.2)) :
    Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
      (Selection.benefit model domain original) reference choice.policy.protocol := by
  constructor
  · exact Selection.acceptance_bounds_every_benefit model domain original _ _ choice.policy.accepted
  · intro backward
    obtain ⟨tail,accepted,better⟩ := available
    obtain ⟨candidate,inside,same⟩ := every_accepted_completion_is_generated model domain original past reference tail accepted
    have maximal := choice.maximal candidate inside
    change ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
      (Selection.benefit model domain original) choice.policy.protocol candidate.protocol at maximal
    rw [same] at maximal
    apply maximal
    constructor
    · intro axis member
      exact (better.1 axis member).trans (backward axis member)
    · intro reverse
      apply better.2
      intro axis member
      exact (backward axis member).trans (reverse axis member)

/-- A previously generated admitted plan retains its own suffix. The restricted
    search cannot invent a blockage by discarding that already paid alternative. -/
theorem an_already_admitted_plan_supplies_its_own_future_completion
    (prior : Selection.Choice model domain original reference) (cut : Nat) :
    ∃ choice, compile model domain original (prior.policy.protocol.controls.take cut) reference = .selected choice := by
  cases result : compile model domain original (prior.policy.protocol.controls.take cut) reference with
  | selected choice => exact ⟨choice,rfl⟩
  | blocked rejected =>
    let tail : Complete.FiniteProgram model.source.code :=
      ⟨(prior.policy.protocol.controls.drop cut).length,Splice.word (prior.policy.protocol.controls.drop cut)⟩
    have same : extension (horizon domain) (prior.policy.protocol.controls.take cut) tail.2 = prior.policy.protocol :=
      (the_committed_plan_is_one_of_its_own_prefix_completions _ _ _).trans
        (Complete.clipping_a_bounded_program_is_itself prior.policy.protocol)
    have accepted : Selection.acceptable model domain original reference
        (extension (horizon domain) (prior.policy.protocol.controls.take cut) tail.2) := by
      rw [same]
      exact prior.policy.accepted
    exact False.elim ((rejected tail).broken (accepted (rejected tail).row (rejected tail).generated))


omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_completion_preserves_the_committed_control_prefix
    (bound : Nat) (past : List (Rule code)) (tail : Program code fuel) (within : past.length ≤ bound) :
    (extension bound past tail).controls.take past.length = past := by
  change ((past++tail.controls).take bound).take past.length = past
  rw [List.take_take,Nat.min_eq_left within,List.take_append_length]

theorem the_selected_plan_really_preserves_the_committed_control_prefix
    (choice : Choice model domain original past reference) (within : past.length ≤ horizon domain) :
    choice.policy.protocol.controls.take past.length = past :=
  every_completion_preserves_the_committed_control_prefix _ _ choice.policy.tail within

/-- This reviewer recomputes the original full tensor. Only immutable past controls
    restrict the proposal catalogue; native anchors still range over all programmes. -/
def verify (tail : Program model.source.code (horizon domain)) : Bool :=
  let programme := extension (horizon domain) past tail
  decide (Selection.acceptable model domain original reference programme ∧
    ∀ other ∈ extensions (horizon domain) past,
      Selection.acceptable model domain original reference other → ¬ Review.improves model domain original programme other)

theorem verify_iff (proposedTail : Program model.source.code (horizon domain)) :
    verify model domain original past reference proposedTail = true ↔
      Selection.acceptable model domain original reference (extension (horizon domain) past proposedTail) ∧
      ∀ tail : Complete.FiniteProgram model.source.code,
        Selection.acceptable model domain original reference (extension (horizon domain) past tail.2) →
          ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
            (Selection.benefit model domain original) (extension (horizon domain) past proposedTail) (extension (horizon domain) past tail.2) := by
  simp only [verify,decide_eq_true_eq]
  constructor
  · rintro ⟨accepted,checked⟩
    refine ⟨accepted,?_⟩
    intro tail supported
    exact fun strict => checked _ (every_finite_tail_is_generated _ _ tail.2) supported
      ((Review.improves_iff _ _ _ _ _).mpr strict)
  · rintro ⟨accepted,checked⟩
    refine ⟨accepted,?_⟩
    intro other inside supported strict
    obtain ⟨tail,_,same⟩ := List.mem_map.mp inside
    subst other
    exact checked ⟨_,tail⟩ supported ((Review.improves_iff _ _ _ _ _).mp strict)

theorem every_selected_completion_is_independently_reviewable
    (choice : Choice model domain original past reference) :
    verify model domain original past reference choice.policy.tail = true := by
  apply (verify_iff _ _ _ _ _ _).mpr
  refine ⟨choice.policy.accepted,?_⟩
  intro tail accepted
  obtain ⟨candidate,inside,same⟩ := every_accepted_completion_is_generated model domain original past reference tail accepted
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
    (Selection.benefit model domain original) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  exact maximal


def Contract : Outcome model domain original past reference → Prop
  | .selected choice => verify model domain original past reference choice.policy.tail = true ∧
      (∀ tail : Complete.FiniteProgram model.source.code,
        Selection.acceptable model domain original choice.policy.protocol (extension (horizon domain) past tail.2) →
          ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain) (Selection.benefit model domain original)
            choice.policy.protocol (extension (horizon domain) past tail.2)) ∧
      ((∃ tail : Complete.FiniteProgram model.source.code,
        Selection.acceptable model domain original reference (extension (horizon domain) past tail.2) ∧
          Distributed.Improves (Selection.axes (fuel := horizon domain) model domain) (Selection.benefit model domain original)
            reference (extension (horizon domain) past tail.2)) →
        Distributed.Improves (Selection.axes (fuel := horizon domain) model domain) (Selection.benefit model domain original)
          reference choice.policy.protocol)
  | .blocked rejected => ∀ tail : Complete.FiniteProgram model.source.code,
      (rejected tail).row ∈ Replanning.rows model domain ∧
        ¬ Selection.holds model domain original reference (extension (horizon domain) past tail.2) (rejected tail).row

theorem every_generated_outcome_has_the_complete_future_contract
    (outcome : Outcome model domain original past reference) : Contract model domain original past reference outcome := by
  cases outcome with
  | selected choice =>
      exact ⟨every_selected_completion_is_independently_reviewable model domain original past reference choice,
        the_generated_choice_has_no_full_responsibility_completion_dominator model domain original past reference choice,
        every_available_full_responsibility_completion_improvement_is_realized model domain original past reference choice⟩
  | blocked rejected => exact fun tail => ⟨(rejected tail).generated,(rejected tail).broken⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
