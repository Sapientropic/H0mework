import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Commitment

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))

abbrev Improves := Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
  (Selection.benefit model domain original)
abbrev NoWorse := Distributed.NoWorse (Selection.axes (fuel := horizon domain) model domain)
  (Selection.benefit model domain original)

def Nondominated (programme : Program model.source.code (horizon domain)) : Prop :=
  ∀ other : Program model.source.code (horizon domain),
    Selection.acceptable model domain original reference other → ¬ Improves model domain original programme other

structure Work where
  past : List (Prefix.Rule model.source.code)
  bounded : past.length ≤ horizon domain
  programme : Program model.source.code (horizon domain)
  accepted : Selection.acceptable model domain original reference programme
  retained : programme.controls.take past.length = past
  maximal : Nondominated model domain original reference programme

private theorem nondomination_survives_a_full_responsibility_improvement
    (old new : Program model.source.code (horizon domain)) (maximal : Nondominated model domain original reference old)
    (accepted : Selection.acceptable model domain original old new) : Nondominated model domain original reference new := by
  intro other supported strict
  apply maximal other supported
  have improved := Selection.acceptance_bounds_every_benefit model domain original old new accepted
  refine ⟨?_,?_⟩
  · intro axis inside
    exact (strict.1 axis inside).trans (improved axis inside)
  · intro reverse
    apply strict.2
    intro axis inside
    exact (improved axis inside).trans (reverse axis inside)

private theorem initial_nondomination
    (choice : Choice model domain original [] reference) : Nondominated model domain original reference choice.policy.protocol := by
  intro other accepted
  have same : extension (horizon domain) [] other = other := by
    change clip (horizon domain) other = other
    exact Complete.clipping_a_bounded_program_is_itself other
  have normalized : Selection.acceptable model domain original reference (extension (horizon domain) [] other) := by
    rw [same];exact accepted
  obtain ⟨candidate,inside,identity⟩ := every_accepted_completion_is_generated model domain original [] reference
    ⟨horizon domain,other⟩ normalized
  have maximal := choice.maximal candidate inside
  change ¬ Improves model domain original choice.policy.protocol candidate.protocol at maximal
  rw [identity,same] at maximal
  exact maximal

inductive Start where
  | ready (work : Work model domain original reference)
  | blocked (rejected : ∀ tail : Complete.FiniteProgram model.source.code,
      Selection.Rejection model domain original reference (extension (horizon domain) [] tail.2))

/-- Initial compilation and every later choice are independent of the actual world and opponent. -/
def start : Start model domain original reference :=
  match compile model domain original [] reference with
  | .selected choice => .ready ⟨[],Nat.zero_le _,choice.policy.protocol,choice.policy.accepted,rfl,
      initial_nondomination model domain original reference choice⟩
  | .blocked rejected => .blocked rejected

variable {model domain original reference}

def advance (work : Work model domain original reference) : Work model domain original reference :=
  if inside : work.past.length < horizon domain then
    let nextPast := (Commitment.padded original work.programme).controls.take (work.past.length+1)
    match result : compile model domain original nextPast work.programme with
    | .selected choice =>
        ⟨nextPast,by simp only [nextPast,List.length_take,Commitment.padded_length];omega,
          choice.policy.protocol,Selection.acceptable_trans model domain original _ _ _ choice.policy.accepted work.accepted,
          the_selected_plan_really_preserves_the_committed_control_prefix model domain original nextPast work.programme choice
            (by simp only [nextPast,List.length_take,Commitment.padded_length];omega),
          nondomination_survives_a_full_responsibility_improvement model domain original reference _ _ work.maximal choice.policy.accepted⟩
    | .blocked rejected => False.elim (by
        obtain ⟨choice,same⟩ := Commitment.every_paid_prefix_retains_the_previous_admitted_completion model domain original
          reference work.programme work.accepted (work.past.length+1)
        rw [result] at same
        cases same)
  else work

def run (work : Work model domain original reference) : Nat → Work model domain original reference
  | 0 => work
  | n+1 => advance (run work n)

theorem advance_really_commits_only_the_current_stage
    (work : Work model domain original reference) (inside : work.past.length < horizon domain) :
    (advance work).past = work.past ++ [work.programme.at original work.past.length] := by
  unfold advance
  rw [dif_pos inside]
  dsimp only
  split
  · exact Commitment.next_prefix original work.programme work.past work.retained inside
  · rename_i rejected impossible
    obtain ⟨choice,same⟩ := Commitment.every_paid_prefix_retains_the_previous_admitted_completion model domain original
      reference work.programme work.accepted (work.past.length+1)
    rw [impossible] at same
    cases same

theorem advance_at_the_full_window_is_identity
    (work : Work model domain original reference) (finished : work.past.length = horizon domain) : advance work = work := by
  unfold advance
  rw [dif_neg (by omega)]

theorem every_generated_prefix_length (work : Work model domain original reference) (n : Nat) :
    (run work n).past.length = min (work.past.length+n) (horizon domain) := by
  induction n with
  | zero => simp only [run,Nat.add_zero,Nat.min_eq_left work.bounded]
  | succ n ih =>
      by_cases inside : (run work n).past.length < horizon domain
      · change (advance (run work n)).past.length = _
        rw [advance_really_commits_only_the_current_stage _ inside,List.length_append,List.length_singleton,ih]
        omega
      · have done : (run work n).past.length = horizon domain := Nat.le_antisymm (run work n).bounded (Nat.le_of_not_gt inside)
        change (advance (run work n)).past.length = _
        rw [advance_at_the_full_window_is_identity _ done,done]
        omega

theorem every_cut_keeps_the_whole_original_reference_and_all_future_opponents
    (work : Work model domain original reference) (n : Nat) :
    Selection.acceptable model domain original reference (run work n).programme ∧
      Nondominated model domain original reference (run work n).programme ∧
      (run work n).programme.controls.take (run work n).past.length = (run work n).past :=
  ⟨(run work n).accepted,(run work n).maximal,(run work n).retained⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling
