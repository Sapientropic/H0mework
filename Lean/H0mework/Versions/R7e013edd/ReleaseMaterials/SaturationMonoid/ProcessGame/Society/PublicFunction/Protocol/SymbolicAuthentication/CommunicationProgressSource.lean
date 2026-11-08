import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRunCost
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthPotential

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationProgressSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
def Clear (past : JointResponse.Stages model) : Prop :=
  UnifiedResponse.Clear model start vocabulary encoding law past ∧ JointResponse.queueClear model start past = true
instance (past : JointResponse.Stages model) : Decidable (Clear model start vocabulary encoding law past) := by
  unfold Clear; infer_instance

-- Actual registration/content credit and untried admitted addresses share the original history.
def rank (past : JointResponse.Stages model) :=
  UnifiedServicePotential.remaining model start vocabulary encoding law past + MixedBirthPotential.rank model start past

theorem actual_extension_cannot_refill_the_communication_rank
    (past later : JointResponse.Stages model) (ordered : past <+: later) :
    rank model start vocabulary encoding law later ≤ rank model start vocabulary encoding law past := by
  have used := UnifiedServicePotential.actual_extension_preserves_used model start vocabulary encoding law past later ordered
  have queue := MixedBirthPotential.actual_extension_cannot_refill_queue_addresses model start past later ordered
  unfold rank UnifiedServicePotential.remaining
  omega

def cost (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :=
  (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action).length - past.length

theorem every_original_dispatch_spends_positive_physical_time
    (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :
    0 < cost model start vocabulary encoding law past action := by
  obtain ⟨tail, same⟩ := UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past action
  have spent := UnifiedRecoveryDispatch.every_action_strictly_spends_the_same_source_fuel model start vocabulary encoding law past action
  have fuel := UnifiedResponse.fuel_after_actual_extension model start past tail
  change JointResponse.fuel model start (past ++ tail) = JointResponse.fuel model start past - tail.length at fuel
  rw [same] at fuel
  unfold cost
  rw [← same, List.length_append]
  omega

-- All terms of this gap are physical stage counts, including multi-stage retry macros.
def waitLimit := law.maxDelay + ForwardResponseClock.width model start + 1
def height (past : JointResponse.Stages model) (idle : Nat) :=
  rank model start vocabulary encoding law past * (waitLimit model start law + 1) + (waitLimit model start law - idle)
def horizon (past : JointResponse.Stages model) := height model start vocabulary encoding law past 0 + 1

def timing : Nat → JointResponse.Stages model → Nat → Bool
  | 0, _, _ => true
  | rounds + 1, past, idle =>
    if Clear model start vocabulary encoding law past then true else
    match UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | .advance action =>
      let after := UnifiedRecoveryDispatch.after model start vocabulary encoding law past action
      decide (idle + cost model start vocabulary encoding law past action ≤ waitLimit model start law) &&
        if rank model start vocabulary encoding law after < rank model start vocabulary encoding law past then
          timing rounds after 0
        else timing rounds after (idle + cost model start vocabulary encoding law past action)
    | _ => false

-- Observe only original dispatcher prefixes. This function does not execute a replacement policy.
def locate : Nat → JointResponse.Stages model → Option Nat
  | rounds, past =>
    if Clear model start vocabulary encoding law past then some 0 else
    match rounds with
    | 0 => none
    | rounds + 1 => match UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
      | .advance action => (locate rounds (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)).map Nat.succ
      | _ => none

theorem every_located_cut_is_an_actual_common_communication_cut
    (rounds index : Nat) (past : JointResponse.Stages model)
    (found : locate model start vocabulary encoding law rounds past = some index) :
    index ≤ rounds ∧ Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past index) := by
  induction rounds generalizing index past with
  | zero =>
    simp only [locate] at found
    split at found
    · have same : index = 0 := (Option.some.inj found).symm
      subst index
      exact ⟨Nat.le_refl _, by rw [atCut, UnifiedRunPrefix.zero_has_the_original_stages]; assumption⟩
    · contradiction
  | succ rounds ih =>
    simp only [locate] at found
    split at found
    · have same : index = 0 := (Option.some.inj found).symm
      subst index
      exact ⟨Nat.zero_le _, by rw [atCut, UnifiedRunPrefix.zero_has_the_original_stages]; assumption⟩
    · cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
      | clear complete => simp only [selected] at found; contradiction
      | exhausted empty => simp only [selected] at found; contradiction
      | advance action =>
        rw [selected] at found
        obtain ⟨n, next, same⟩ := Option.map_eq_some_iff.mp found
        subst index
        obtain ⟨bound, clear⟩ := ih n _ next
        exact ⟨by omega, by simpa only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected] using clear⟩

theorem checked_source_timing_generates_a_common_communication_cut
    (rounds idle : Nat) (past : JointResponse.Stages model)
    (inside : idle ≤ waitLimit model start law)
    (enough : height model start vocabulary encoding law past idle < rounds)
    (checked : timing model start vocabulary encoding law rounds past idle = true) :
    (locate model start vocabulary encoding law rounds past).isSome = true := by
  induction rounds generalizing past idle with
  | zero => omega
  | succ rounds ih =>
    by_cases clear : Clear model start vocabulary encoding law past
    · simp only [locate, if_pos clear, Option.isSome_some]
    · simp only [timing, if_neg clear] at checked
      cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
      | clear complete => simp only [selected] at checked; contradiction
      | exhausted empty => simp only [selected] at checked; contradiction
      | advance action =>
        let after := UnifiedRecoveryDispatch.after model start vocabulary encoding law past action
        have monotone := actual_extension_cannot_refill_the_communication_rank model start vocabulary encoding law past after
          (UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past action)
        have elapsed := every_original_dispatch_spends_positive_physical_time model start vocabulary encoding law past action
        rw [selected] at checked
        change (decide (idle + cost model start vocabulary encoding law past action ≤ waitLimit model start law) &&
          if rank model start vocabulary encoding law after < rank model start vocabulary encoding law past then
            timing model start vocabulary encoding law rounds after 0 else
            timing model start vocabulary encoding law rounds after (idle + cost model start vocabulary encoding law past action)) = true at checked
        simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
        simp only [locate, if_neg clear, selected, Option.isSome_map]
        change (locate model start vocabulary encoding law rounds after).isSome = true
        by_cases progress : rank model start vocabulary encoding law after < rank model start vocabulary encoding law past
        · simp only [if_pos progress] at checked
          apply ih 0 after (Nat.zero_le _) _ checked.2
          have drop := Nat.mul_le_mul_right (waitLimit model start law + 1) (Nat.succ_le_of_lt progress)
          simp only [Nat.succ_mul] at drop
          unfold height at enough ⊢
          omega
        · simp only [if_neg progress] at checked
          apply ih (idle + cost model start vocabulary encoding law past action) after checked.1 _ checked.2
          unfold height at enough ⊢
          have same : rank model start vocabulary encoding law after = rank model start vocabulary encoding law past := by omega
          rw [same]
          omega

theorem the_source_generated_horizon_suffices
    (past : JointResponse.Stages model)
    (checked : timing model start vocabulary encoding law (horizon model start vocabulary encoding law past) past 0 = true) :
    ∃ index, locate model start vocabulary encoding law (horizon model start vocabulary encoding law past) past = some index ∧
      index ≤ horizon model start vocabulary encoding law past ∧
      Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past index) := by
  have present := checked_source_timing_generates_a_common_communication_cut model start vocabulary encoding law
    (horizon model start vocabulary encoding law past) 0 past (Nat.zero_le _) (by unfold horizon; omega) checked
  cases found : locate model start vocabulary encoding law (horizon model start vocabulary encoding law past) past with
  | none => rw [found] at present; cases present
  | some index => exact ⟨index, rfl, every_located_cut_is_an_actual_common_communication_cut model start vocabulary encoding law _ _ _ found⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationProgressSource
