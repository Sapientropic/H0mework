import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceStanding

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceRoster

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := ForwardResponseClock.width model start

theorem a_communication_clear_original_advance_is_one_stage
    (past : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (clear : UnifiedResponse.Clear model start vocabulary encoding law past)
    (selected : JointResponse.step model start vocabulary encoding law past = .advance action) :
    ∃ stage, JointResponse.after model start vocabulary encoding law past action = past ++ [stage] := by
  cases action with
  | withdrawal ready accepted actual => exact ⟨_, rfl⟩
  | refused ready denied actual => exact ⟨_, rfl⟩
  | wait live => exact ⟨_, rfl⟩
  | communication action =>
    exfalso
    unfold JointResponse.step at selected
    split at selected
    · contradiction
    · split at selected
      · simp only [UnifiedResponse.step, dif_pos clear] at selected
        split at selected
        · split at selected <;> cases selected
        · cases selected
      · contradiction

theorem a_communication_clear_actual_dispatch_is_one_stage
    (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (clear : UnifiedResponse.Clear model start vocabulary encoding law past)
    (selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .advance action) :
    ∃ stage, UnifiedRecoveryDispatch.after model start vocabulary encoding law past action = past ++ [stage] := by
  cases action with
  | recovery answer => exact ⟨_, rfl⟩
  | original action =>
    exact a_communication_clear_original_advance_is_one_stage model start vocabulary encoding law past action clear
      (UnifiedServicePotential.original_selection_is_retained model start vocabulary encoding law past action selected)

theorem clear_communication_makes_actual_trace_and_physical_clock_agree
    (rounds : Nat) (past : JointResponse.Stages model)
    (clear : ∀ n < rounds, UnifiedResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past n)) :
    (atCut model start vocabulary encoding law past rounds).length = past.length +
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).trace.length := by
  induction rounds generalizing past with
  | zero => simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run]; split_ifs <;> simp
  | succ rounds ih =>
    have here := clear 0 (by omega)
    rw [atCut, UnifiedRunPrefix.zero_has_the_original_stages] at here
    cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected, List.length_nil, Nat.add_zero]
    | exhausted empty => simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected, List.length_nil, Nat.add_zero]
    | advance action =>
      let next := UnifiedRecoveryDispatch.after model start vocabulary encoding law past action
      have shifted : ∀ n < rounds, UnifiedResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law next n) := by
        intro n inside
        have old := clear (1 + n) (by omega)
        have same := UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law 1 n past
        have first : UnifiedRunPrefix.atCut model start vocabulary encoding law past 1 = next := by
          change (UnifiedRecoveryRun.run model start vocabulary encoding law 1 past).stages = next
          simp only [UnifiedRecoveryRun.run, selected]
          exact UnifiedRunPrefix.zero_has_the_original_stages model start vocabulary encoding law next
        rw [first] at same
        change UnifiedResponse.Clear model start vocabulary encoding law
          (UnifiedRunPrefix.atCut model start vocabulary encoding law next n)
        rw [← same]
        exact old
      have paid := ih next shifted
      obtain ⟨stage, single⟩ := a_communication_clear_actual_dispatch_is_one_stage model start vocabulary encoding law past action here selected
      have cost : next.length = past.length + 1 := by rw [show next = past ++ [stage] from single, List.length_append]; rfl
      simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected, List.length_cons]
      change (atCut model start vocabulary encoding law next rounds).length =
        past.length + ((UnifiedRecoveryRun.run model start vocabulary encoding law rounds next).trace.length + 1)
      omega

theorem an_unclear_final_cut_has_no_clear_earlier_cut
    (rounds n : Nat) (past : JointResponse.Stages model) (inside : n ≤ rounds)
    (unfinished : ¬ JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds)) :
    ¬ JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past n) := by
  intro clear
  have same := UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law n (rounds - n) past
  rw [Nat.add_sub_of_le inside, UnifiedRunPrefix.a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law _ clear] at same
  have aligned : atCut model start vocabulary encoding law past rounds =
      atCut model start vocabulary encoding law past n := same
  exact unfinished (aligned.symm ▸ clear)

theorem clear_communication_generates_the_actual_receiver_slot
    (past : JointResponse.Stages model) (worker : Fin model.source.code.sites)
    (clear : ∀ n < width model start,
      UnifiedResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past n))
    (full : (UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) past).trace.length = width model start) :
    ∃ n < width model start,
      Distributed.Recall.Information.Agency.ownerAt model.source.code
        (EventHistory.execute start (atCut model start vocabulary encoding law past n)).ownerStart
        (EventStep.seed (EventHistory.execute start (atCut model start vocabulary encoding law past n))).history.length = some worker := by
  let cursor := EventHistory.execute start past
  let delay := SilentWindow.delay cursor worker
  have arrived := SilentWindow.the_actual_receiver_owns_the_generated_arrival cursor worker
  have quiet := SilentWindow.preserves_the_actual_state cursor delay
  rw [quiet.roster, quiet.history] at arrived
  have bounded := SilentWindow.the_generated_delay_has_a_source_roster_bound cursor worker
  have origin := (ForwardResponseClock.actual_list_clocks model start past).2
  have inside : delay < width model start := by
    change cursor.ownerStart = start.ownerStart at origin
    dsimp only [width, ForwardResponseClock.width]
    change delay < cursor.ownerStart - (EventStep.seed cursor).history.length + 4 * model.source.code.sites at bounded
    omega
  refine ⟨delay, inside, ?_⟩
  have short := UnifiedRunPrefix.every_prefix_of_a_full_actual_trace_is_full model start vocabulary encoding law
    (width model start) delay past (Nat.le_of_lt inside) full
  have paid := clear_communication_makes_actual_trace_and_physical_clock_agree model start vocabulary encoding law delay past
    (fun n hn => clear n (by omega))
  rw [short] at paid
  have actual := ForwardResponseClock.actual_list_clocks model start (atCut model start vocabulary encoding law past delay)
  have before := ForwardResponseClock.actual_list_clocks model start past
  rw [actual.2, actual.1, paid]
  change Distributed.Recall.Information.Agency.ownerAt model.source.code start.ownerStart
    ((EventStep.seed start).history.length + (past.length + delay)) = some worker
  have oldHistory : (EventStep.seed cursor).history.length = (EventStep.seed start).history.length + past.length := before.1
  have oldRoster : cursor.ownerStart = start.ownerStart := before.2
  rw [oldRoster, oldHistory] at arrived
  simpa only [Nat.add_assoc] using arrived

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceRoster
