import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServicePotential

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceWindow
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

def physical (rounds : Nat) (past : JointResponse.Stages model) :=
  SignatureClock.tally model start vocabulary encoding law past
    ((UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages.drop past.length)

theorem the_same_actual_mixed_history_pays_for_every_signature_opportunity
    (rounds : Nat) (past : JointResponse.Stages model) :
    UnifiedServicePotential.used model start vocabulary encoding law past +
      physical model start vocabulary encoding law rounds past ≤
    UnifiedServicePotential.used model start vocabulary encoding law
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero =>
    simp only [physical, UnifiedRecoveryRun.run]
    split
    · simp only [List.drop_length, SignatureClock.tally, Nat.add_zero, Nat.le_refl]
    · split <;> simp only [List.drop_length, SignatureClock.tally, Nat.add_zero, Nat.le_refl]
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [physical, UnifiedRecoveryRun.run, actual, List.drop_length, SignatureClock.tally, Nat.add_zero, Nat.le_refl]
    | exhausted empty => simp only [physical, UnifiedRecoveryRun.run, actual, List.drop_length, SignatureClock.tally, Nat.add_zero, Nat.le_refl]
    | advance action =>
      obtain ⟨more, afterExact⟩ := UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past action
      obtain ⟨tail, finalExact⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds
        (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      have paid := UnifiedServicePotential.every_selected_macro_pays_for_its_actual_signature_opportunities model start vocabulary encoding law
        past more action actual afterExact
      have next := ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      unfold physical at next
      rw [← finalExact, List.drop_left] at next
      simp only [physical, UnifiedRecoveryRun.run, actual]
      rw [← finalExact, ← afterExact, List.append_assoc, List.drop_left, SignatureClock.tally_append, afterExact]
      rw [← List.append_assoc, afterExact]
      omega

theorem original_identities_bound_all_mixed_signature_opportunities
    (rounds : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages) :
    physical model start vocabulary encoding law rounds past ≤
      UnifiedServicePotential.remaining model start vocabulary encoding law past := by
  have paid := the_same_actual_mixed_history_pays_for_every_signature_opportunity model start vocabulary encoding law rounds past
  have bound := UnifiedServicePotential.actual_compliant_history_has_the_original_capacity model start vocabulary encoding law
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages delay compliant
  unfold UnifiedServicePotential.remaining
  omega

def deadline (past : JointResponse.Stages model) :=
  ForwardResponseClock.width model start * (UnifiedServicePotential.remaining model start vocabulary encoding law past + 1)

theorem primitive_source_conditions_generate_a_live_signature_cut_in_the_unified_execution
    (past : JointResponse.Stages model) (delay : Nat)
    (reserve : deadline model start vocabulary encoding law past + 1 ≤ JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages)
    (available : SignatureClock.Available model start vocabulary encoding law past
      ((UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages.drop past.length)) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
    ∃ n, past.length ≤ n ∧ n ≤ past.length + deadline model start vocabulary encoding law past ∧
      n ≤ full.length ∧ SignatureEligibility.Clear model start vocabulary encoding law (full.take n) ∧
      0 < JointResponse.fuel model start (full.take n) := by
  dsimp only
  let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
  let window := deadline model start vocabulary encoding law past
  obtain ⟨more, exactFull⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law
    (JointResponse.fuel model start past) past
  change past ++ more = full at exactFull
  have availability : SignatureClock.Available model start vocabulary encoding law past more := by
    change SignatureClock.Available model start vocabulary encoding law past (full.drop past.length) at available
    simpa only [← exactFull, List.drop_left] using available
  have cut : ∀ n, full.take (past.length + n) = past ++ more.take n := by
    intro n; rw [← exactFull]; simp [List.take_append]
  have someCut : ∃ n ≤ window, n ≤ more.length ∧ SignatureEligibility.Clear model start vocabulary encoding law (past ++ more.take n) := by
    by_cases room : window ≤ more.length
    · have upper := original_identities_bound_all_mixed_signature_opportunities model start vocabulary encoding law
        (JointResponse.fuel model start past) past delay compliant
      unfold physical at upper
      change SignatureClock.tally model start vocabulary encoding law past (full.drop past.length) ≤ _ at upper
      rw [← exactFull, List.drop_left] at upper
      obtain ⟨n, inside, clear⟩ := SignatureWindow.actual_opportunity_budget_generates_a_common_clear_cut model start vocabulary encoding law
        past more (UnifiedServicePotential.remaining model start vocabulary encoding law past) room upper availability
      change n ≤ window at inside
      exact ⟨n, inside, by omega, clear⟩
    · have live : JointResponse.fuel model start full ≠ 0 := by
        intro empty
        have fuel := UnifiedResponse.fuel_after_actual_extension model start past more
        change JointResponse.fuel model start (past ++ more) = JointResponse.fuel model start past - more.length at fuel
        rw [exactFull, empty] at fuel
        omega
      have result := UnifiedRecoveryRun.the_source_generates_joint_completion_or_actual_exhaustion model start vocabulary encoding law past
      have complete : (UnifiedRecoveryRun.produce model start vocabulary encoding law past).status = .jointComplete := by
        rcases result with complete | exhausted
        · exact complete
        · exact False.elim (live exhausted.2)
      have gates := (UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law
        (JointResponse.fuel model start past) past complete).1
      refine ⟨more.length, by omega, Nat.le_refl _, ?_⟩
      rw [List.take_length, exactFull]
      exact ⟨gates.1, gates.2.1⟩
  obtain ⟨n, inside, enough, clear⟩ := someCut
  refine ⟨past.length + n, by omega, by omega, ?_, ?_, ?_⟩
  · have size := congrArg List.length exactFull
    simp only [List.length_append] at size
    change past.length + n ≤ full.length
    omega
  · rw [cut]; exact clear
  · rw [cut]
    have fuel := UnifiedResponse.fuel_after_actual_extension model start past (more.take n)
    change JointResponse.fuel model start (past ++ more.take n) = JointResponse.fuel model start past - (more.take n).length at fuel
    rw [List.length_take, Nat.min_eq_left enough] at fuel
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceWindow
