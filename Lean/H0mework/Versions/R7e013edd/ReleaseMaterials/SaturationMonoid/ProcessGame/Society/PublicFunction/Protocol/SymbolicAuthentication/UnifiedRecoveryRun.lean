import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryDispatch

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryRun
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

abbrev Stages := JointResponse.Stages model
abbrev Status := JointResponseRun.Status

structure RecoveryEvent where
  private mk ::
  past : Stages model
  answer : NativeRecovery.Ready model start past vocabulary encoding law

def events (past : Stages model) : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past →
    List (RecoveryEvent model start vocabulary encoding law)
  | .original _ => []
  | .recovery answer => [⟨past, answer⟩]

structure Result where
  private mk ::
  stages : Stages model
  status : Status
  trace : List UnifiedRecoveryDispatch.Kind
  recoveries : List (RecoveryEvent model start vocabulary encoding law)

def run : Nat → Stages model → Result model start vocabulary encoding law
  | 0, past =>
    if JointResponse.Clear model start vocabulary encoding law past then ⟨past, .jointComplete, [], []⟩
    else if JointResponse.fuel model start past = 0 then ⟨past, .exhausted, [], []⟩
    else ⟨past, .observationCut, [], []⟩
  | rounds + 1, past => match UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | .clear _ => ⟨past, .jointComplete, [], []⟩
    | .exhausted _ => ⟨past, .exhausted, [], []⟩
    | .advance action =>
      let next := run rounds (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      ⟨next.stages, next.status, UnifiedRecoveryDispatch.kind model start vocabulary encoding law action :: next.trace,
        events model start vocabulary encoding law past action ++ next.recoveries⟩

def produce (past : Stages model) := run model start vocabulary encoding law (JointResponse.fuel model start past) past

theorem every_run_keeps_the_whole_actual_history (rounds : Nat) (past : Stages model) :
    past <+: (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run]; split <;> first | exact List.prefix_refl _ | split <;> exact List.prefix_refl _
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [run, actual]; exact List.prefix_refl _
    | exhausted empty => simp only [run, actual]; exact List.prefix_refl _
    | advance action =>
      simp only [run, actual]
      exact (UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past action).trans (ih _)

theorem completion_contains_all_original_joint_gates (rounds : Nat) (past : Stages model)
    (complete : (run model start vocabulary encoding law rounds past).status = .jointComplete) :
    JointResponse.Clear model start vocabulary encoding law (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at complete ⊢; (split_ifs at complete ⊢; simp_all)
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past <;>
      simp only [run, actual] at complete ⊢ <;> try contradiction
    · assumption
    · exact ih _ complete

theorem every_unified_macro_is_paid_from_the_same_source_fuel (rounds : Nat) (past : Stages model) :
    (run model start vocabulary encoding law rounds past).trace.length ≤ JointResponse.fuel model start past := by
  induction rounds generalizing past with
  | zero => simp only [run]; split_ifs <;> exact Nat.zero_le _
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [run, actual, List.length_nil]; exact Nat.zero_le _
    | exhausted empty => simp only [run, actual, List.length_nil]; exact Nat.zero_le _
    | advance action =>
      have spent := UnifiedRecoveryDispatch.every_action_strictly_spends_the_same_source_fuel model start vocabulary encoding law past action
      have next := ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      simp only [run, actual, List.length_cons]
      omega

theorem source_sized_observation_cuts_have_no_actual_fuel (rounds : Nat) (past : Stages model)
    (room : JointResponse.fuel model start past ≤ rounds)
    (cut : (run model start vocabulary encoding law rounds past).status = .observationCut) :
    JointResponse.fuel model start (run model start vocabulary encoding law rounds past).stages = 0 := by
  induction rounds generalizing past with
  | zero => simp only [run] at cut ⊢; (split_ifs at cut ⊢; simp_all)
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past <;>
      simp only [run, actual] at cut ⊢ <;> try contradiction
    rename_i action
    have spent := UnifiedRecoveryDispatch.every_action_strictly_spends_the_same_source_fuel model start vocabulary encoding law past action
    exact ih _ (by omega) cut

theorem observation_cuts_retain_positive_actual_fuel (rounds : Nat) (past : Stages model)
    (cut : (run model start vocabulary encoding law rounds past).status = .observationCut) :
    0 < JointResponse.fuel model start (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at cut ⊢; (split_ifs at cut ⊢; simp_all; omega)
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past <;>
      simp only [run, actual] at cut ⊢ <;> try contradiction
    exact ih _ cut

theorem exhausted_runs_have_zero_actual_fuel (rounds : Nat) (past : Stages model)
    (empty : (run model start vocabulary encoding law rounds past).status = .exhausted) :
    JointResponse.fuel model start (run model start vocabulary encoding law rounds past).stages = 0 := by
  induction rounds generalizing past with
  | zero => simp only [run] at empty ⊢; (split_ifs at empty ⊢; simp_all)
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past <;>
      simp only [run, actual] at empty ⊢ <;> try contradiction
    · assumption
    · exact ih _ empty

theorem the_source_generates_joint_completion_or_actual_exhaustion (past : Stages model) :
    (produce model start vocabulary encoding law past).status = .jointComplete ∨
      ((produce model start vocabulary encoding law past).status = .exhausted ∧
        JointResponse.fuel model start (produce model start vocabulary encoding law past).stages = 0) := by
  cases actual : (produce model start vocabulary encoding law past).status with
  | jointComplete => exact Or.inl rfl
  | exhausted => exact Or.inr ⟨rfl, exhausted_runs_have_zero_actual_fuel model start vocabulary encoding law _ past actual⟩
  | observationCut =>
    have live := observation_cuts_retain_positive_actual_fuel model start vocabulary encoding law _ past actual
    have empty := source_sized_observation_cuts_have_no_actual_fuel model start vocabulary encoding law
      (JointResponse.fuel model start past) past (Nat.le_refl _) actual
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryRun
