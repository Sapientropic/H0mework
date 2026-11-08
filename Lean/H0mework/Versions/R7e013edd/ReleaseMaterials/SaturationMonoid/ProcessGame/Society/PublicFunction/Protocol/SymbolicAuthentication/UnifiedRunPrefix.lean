import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeServiceForward

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRunPrefix
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

abbrev atCut (past : JointResponse.Stages model) (rounds : Nat) :=
  (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages

def nextStages (past : JointResponse.Stages model) :=
  match UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
  | .advance action => UnifiedRecoveryDispatch.after model start vocabulary encoding law past action
  | _ => past

theorem zero_has_the_original_stages (past : JointResponse.Stages model) : atCut model start vocabulary encoding law past 0 = past := by
  simp only [atCut, UnifiedRecoveryRun.run]
  split
  · rfl
  · split <;> rfl

theorem a_clear_cut_stays_at_the_same_actual_stages (past : JointResponse.Stages model)
    (closed : JointResponse.Clear model start vocabulary encoding law past) (rounds : Nat) :
    atCut model start vocabulary encoding law past rounds = past := by
  cases rounds with
  | zero => exact zero_has_the_original_stages model start vocabulary encoding law past
  | succ rounds => simp only [atCut, UnifiedRecoveryRun.run, UnifiedRecoveryDispatch.step, dif_pos closed]

private theorem an_exhausted_cut_stays_at_the_same_actual_stages (past : JointResponse.Stages model)
    (empty : JointResponse.fuel model start past = 0) (rounds : Nat) :
    atCut model start vocabulary encoding law past rounds = past := by
  cases rounds with
  | zero => exact zero_has_the_original_stages model start vocabulary encoding law past
  | succ rounds =>
    by_cases closed : JointResponse.Clear model start vocabulary encoding law past
    · exact a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed _
    · have actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .exhausted empty := by
        unfold UnifiedRecoveryDispatch.step
        simp only [dif_neg closed]
        split
        · split
          · rename_i answer selected
            have live := answer.material.live
            change 0 < JointResponse.fuel model start past at live
            omega
          · unfold UnifiedRecoveryDispatch.original
            simp only [JointResponse.step, dif_neg closed, dif_neg (by omega : ¬ 0 < JointResponse.fuel model start past)]
        · unfold UnifiedRecoveryDispatch.original
          simp only [JointResponse.step, dif_neg closed, dif_neg (by omega : ¬ 0 < JointResponse.fuel model start past)]
      simp only [atCut, UnifiedRecoveryRun.run, actual]

theorem actual_run_prefixes_compose (first later : Nat) (past : JointResponse.Stages model) :
    atCut model start vocabulary encoding law past (first + later) =
      atCut model start vocabulary encoding law (atCut model start vocabulary encoding law past first) later := by
  induction first generalizing past with
  | zero => simp only [Nat.zero_add, zero_has_the_original_stages]
  | succ first ih =>
    cases observed : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear closed =>
      rw [a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed (first + 1 + later),
        a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed (first + 1),
        a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed later]
    | exhausted empty =>
      rw [an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty (first + 1 + later),
        an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty (first + 1),
        an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty later]
    | advance action =>
      simpa only [Nat.succ_add, atCut, UnifiedRecoveryRun.run, observed] using
        ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)

theorem the_next_actual_prefix_is_the_same_original_step (rounds : Nat) (past : JointResponse.Stages model) :
    atCut model start vocabulary encoding law past (rounds + 1) =
      nextStages model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds) := by
  rw [actual_run_prefixes_compose]
  cases observed : UnifiedRecoveryDispatch.step model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds) with
  | clear closed => simp only [atCut, UnifiedRecoveryRun.run, nextStages, observed]
  | exhausted empty => simp only [atCut, UnifiedRecoveryRun.run, nextStages, observed]
  | advance action =>
    simp only [atCut, UnifiedRecoveryRun.run, nextStages, observed]
    exact zero_has_the_original_stages model start vocabulary encoding law _

theorem records_at_zero (past : JointResponse.Stages model) :
    NativeServiceTrace.records model start vocabulary encoding law 0 past = [] := rfl

private theorem stopped_records (past : JointResponse.Stages model) (rounds : Nat)
    (stopped : JointResponse.Clear model start vocabulary encoding law past ∨ JointResponse.fuel model start past = 0) :
    NativeServiceTrace.records model start vocabulary encoding law rounds past = [] := by
  cases rounds with
  | zero => rfl
  | succ rounds =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [NativeServiceTrace.records, actual]
    | exhausted empty => simp only [NativeServiceTrace.records, actual]
    | advance action =>
      rcases stopped with closed | empty
      · simp only [UnifiedRecoveryDispatch.step, dif_pos closed] at actual
        contradiction
      · have spent := UnifiedRecoveryDispatch.every_action_strictly_spends_the_same_source_fuel model start vocabulary encoding law past action
        omega

theorem actual_service_records_compose (first later : Nat) (past : JointResponse.Stages model) :
    NativeServiceTrace.records model start vocabulary encoding law (first + later) past =
      NativeServiceTrace.records model start vocabulary encoding law first past ++
      NativeServiceTrace.records model start vocabulary encoding law later (atCut model start vocabulary encoding law past first) := by
  induction first generalizing past with
  | zero => simp only [Nat.zero_add, records_at_zero, List.nil_append, zero_has_the_original_stages]
  | succ first ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear closed =>
      rw [a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed]
      simp only [Nat.succ_add, NativeServiceTrace.records, actual, List.nil_append]
      exact (stopped_records model start vocabulary encoding law past later (Or.inl closed)).symm
    | exhausted empty =>
      rw [an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty]
      simp only [Nat.succ_add, NativeServiceTrace.records, actual, List.nil_append]
      exact (stopped_records model start vocabulary encoding law past later (Or.inr empty)).symm
    | advance action =>
      simp only [Nat.succ_add, NativeServiceTrace.records, actual, atCut, UnifiedRecoveryRun.run]
      rw [ih]
      exact (List.append_assoc ..).symm

theorem observation_cut_has_all_its_actual_invocations (rounds : Nat) (past : JointResponse.Stages model)
    (cut : (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).status = .observationCut) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).trace.length = rounds := by
  induction rounds generalizing past with
  | zero => simp only [UnifiedRecoveryRun.run] at cut ⊢; split_ifs at cut ⊢; simp_all
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past <;>
      simp only [UnifiedRecoveryRun.run, actual] at cut ⊢ <;> try contradiction
    rw [List.length_cons, ih _ cut]

theorem stopped_trace (past : JointResponse.Stages model) (rounds : Nat)
    (stopped : JointResponse.Clear model start vocabulary encoding law past ∨ JointResponse.fuel model start past = 0) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).trace = [] := by
  cases rounds with
  | zero => simp only [UnifiedRecoveryRun.run]; split_ifs <;> rfl
  | succ rounds =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [UnifiedRecoveryRun.run, actual]
    | exhausted empty => simp only [UnifiedRecoveryRun.run, actual]
    | advance action =>
      rcases stopped with closed | empty
      · simp only [UnifiedRecoveryDispatch.step, dif_pos closed] at actual
        contradiction
      · have spent := UnifiedRecoveryDispatch.every_action_strictly_spends_the_same_source_fuel model start vocabulary encoding law past action
        omega

theorem actual_trace_lengths_compose (first later : Nat) (past : JointResponse.Stages model) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law (first + later) past).trace.length =
      (UnifiedRecoveryRun.run model start vocabulary encoding law first past).trace.length +
      (UnifiedRecoveryRun.run model start vocabulary encoding law later (atCut model start vocabulary encoding law past first)).trace.length := by
  induction first generalizing past with
  | zero => simp only [Nat.zero_add, zero_has_the_original_stages, UnifiedRecoveryRun.run]; split_ifs <;> simp only [List.length_nil, Nat.zero_add]
  | succ first ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear closed =>
      rw [a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed]
      simp only [Nat.succ_add, UnifiedRecoveryRun.run, actual, List.length_nil, Nat.zero_add]
      rw [stopped_trace model start vocabulary encoding law past later (Or.inl closed)]
      rfl
    | exhausted empty =>
      rw [an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty]
      simp only [Nat.succ_add, UnifiedRecoveryRun.run, actual, List.length_nil, Nat.zero_add]
      rw [stopped_trace model start vocabulary encoding law past later (Or.inr empty)]
      rfl
    | advance action =>
      simp only [Nat.succ_add, UnifiedRecoveryRun.run, actual, List.length_cons, atCut]
      have same := ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      dsimp only [atCut] at same
      omega

theorem actual_trace_length_is_bounded_by_invocations (rounds : Nat) (past : JointResponse.Stages model) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).trace.length ≤ rounds := by
  induction rounds generalizing past with
  | zero => simp only [UnifiedRecoveryRun.run]; split_ifs <;> exact Nat.zero_le _
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past <;>
      simp only [UnifiedRecoveryRun.run, actual, List.length_nil, List.length_cons] <;> try omega
    exact Nat.add_le_add_right (ih _) 1

theorem every_prefix_of_a_full_actual_trace_is_full (rounds first : Nat) (past : JointResponse.Stages model)
    (inside : first ≤ rounds)
    (full : (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).trace.length = rounds) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law first past).trace.length = first := by
  have same := actual_trace_lengths_compose model start vocabulary encoding law first (rounds - first) past
  rw [Nat.add_sub_of_le inside] at same
  have before := actual_trace_length_is_bounded_by_invocations model start vocabulary encoding law first past
  have after := actual_trace_length_is_bounded_by_invocations model start vocabulary encoding law (rounds - first)
    (atCut model start vocabulary encoding law past first)
  omega

theorem clear_final_stages_have_joint_complete_status (rounds : Nat) (past : JointResponse.Stages model)
    (clear : JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds)) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).status = .jointComplete := by
  induction rounds generalizing past with
  | zero =>
    rw [zero_has_the_original_stages] at clear
    simp only [UnifiedRecoveryRun.run, if_pos clear]
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear closed => simp only [UnifiedRecoveryRun.run, actual]
    | exhausted empty =>
      have same := an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty (rounds + 1)
      rw [same] at clear
      simp only [UnifiedRecoveryDispatch.step, dif_pos clear] at actual
      contradiction
    | advance action =>
      simp only [atCut, UnifiedRecoveryRun.run, actual] at clear ⊢
      exact ih _ clear

theorem completed_prefix_is_the_same_full_source_run (rounds : Nat) (past : JointResponse.Stages model)
    (inside : rounds ≤ JointResponse.fuel model start past)
    (complete : (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).status = .jointComplete) :
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages = atCut model start vocabulary encoding law past rounds ∧
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).status = .jointComplete := by
  have closed := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law rounds past complete
  have same := actual_run_prefixes_compose model start vocabulary encoding law rounds (JointResponse.fuel model start past - rounds) past
  rw [Nat.add_sub_of_le inside, a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law _ closed] at same
  refine ⟨same, ?_⟩
  apply clear_final_stages_have_joint_complete_status model start vocabulary encoding law (JointResponse.fuel model start past) past
  rw [same]
  exact closed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRunPrefix
