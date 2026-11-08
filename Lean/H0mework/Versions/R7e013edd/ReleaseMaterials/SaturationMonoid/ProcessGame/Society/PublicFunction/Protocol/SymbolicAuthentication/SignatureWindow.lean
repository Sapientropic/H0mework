import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureClock

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureWindow
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RejectionProgress

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem a_pending_signature_forces_an_opportunity_in_the_next_actual_roster_block
    (past more : JointResponse.Stages model)
    (room : ForwardResponseClock.width model start ≤ more.length)
    (pending : ¬ SignatureEligibility.Clear model start vocabulary encoding law past)
    (available : SignatureClock.Available model start vocabulary encoding law past more) :
    0 < SignatureClock.tally model start vocabulary encoding law past more := by
  by_contra absent
  have zero : SignatureClock.tally model start vocabulary encoding law past more = 0 := by omega
  have journals : ∀ n, IncidentResponse.journal model start (past ++ more.take n) vocabulary encoding law =
        IncidentResponse.journal model start past vocabulary encoding law ∧
      RejectionResponse.journal model start (past ++ more.take n) vocabulary encoding law =
        RejectionResponse.journal model start past vocabulary encoding law := by
    intro n
    have partition := SignatureClock.tally_append model start vocabulary encoding law past (more.take n) (more.drop n)
    rw [List.take_append_drop] at partition
    exact SignatureClock.zero_actual_opportunities_keeps_both_original_journals model start vocabulary encoding law past (more.take n) (by omega)
  cases first : (UnifiedResponse.incidents model start vocabulary encoding law past).head? with
  | some head =>
    obtain ⟨n, short, inside, owned⟩ := ForwardResponseClock.every_actual_roster_block_has_the_original_receivers_slot
      model start past more head.receiver room
    have survives := SignatureHistory.the_first_unhandled_incident_survives_without_registration model start vocabulary encoding law
      past (past ++ more.take n) (List.prefix_append _ _) head first (journals n).1
    have needed : SignatureClock.Needed model start vocabulary encoding law (past ++ more.take n) head.receiver := by
      exact Or.inl (by rw [survives]; rfl)
    have resources := available ⟨n, inside⟩ head.receiver owned needed
    have eligible : SignatureEligibility.eligible model start vocabulary encoding law (past ++ more.take n) = true := by
      simp only [SignatureEligibility.eligible, SignatureEligibility.incident, survives, owned,
        decide_eq_true_eq, Bool.or_eq_true]
      exact Or.inl ⟨True.intro, resources⟩
    have positive := SignatureClock.an_eligible_actual_prefix_is_counted model start vocabulary encoding law past more n inside eligible
    omega
  | none =>
    have incidents : UnifiedResponse.incidents model start vocabulary encoding law past = [] := List.head?_eq_none_iff.mp first
    have rejects : UnifiedResponse.rejections model start vocabulary encoding law past ≠ [] := by
      intro empty
      exact pending ⟨incidents, empty⟩
    obtain ⟨id, member⟩ := List.exists_mem_of_ne_nil _ rejects
    obtain ⟨born, unhandled⟩ := (unhandled_membership model start vocabulary encoding law past id).mp member
    obtain ⟨n, short, inside, owned⟩ := ForwardResponseClock.every_actual_roster_block_has_the_original_receivers_slot
      model start past more id.1 room
    have unhandledNow : id ∉ handled model start vocabulary encoding law (past ++ more.take n) := by
      simpa only [handled, (journals n).2] using unhandled
    have localPending := ForwardResponseWindow.an_actual_unhandled_identity_has_local_pending_evidence model start vocabulary encoding law
      (past ++ more.take n) id
      (rejection_births_never_disappear model start vocabulary encoding law _ _ (List.prefix_append _ _) born) unhandledNow
    have resources := available ⟨n, inside⟩ id.1 owned (Or.inr localPending)
    have eligible : SignatureEligibility.eligible model start vocabulary encoding law (past ++ more.take n) = true := by
      simp only [SignatureEligibility.eligible, Bool.or_eq_true]
      right
      simp only [ResponseEligibility.eligible, owned, Bool.and_eq_true_iff, decide_eq_true_eq]
      exact ⟨by simpa only [Bool.not_eq_true', List.isEmpty_eq_false_iff] using localPending, resources⟩
    have positive := SignatureClock.an_eligible_actual_prefix_is_counted model start vocabulary encoding law past more n inside eligible
    omega

theorem a_run_without_a_common_clear_cut_pays_once_per_actual_roster_block
    (past more : JointResponse.Stages model) (blocks : Nat)
    (room : ForwardResponseClock.width model start * blocks ≤ more.length)
    (pending : ∀ n ≤ more.length, ¬ SignatureEligibility.Clear model start vocabulary encoding law (past ++ more.take n))
    (available : SignatureClock.Available model start vocabulary encoding law past more) :
    blocks ≤ SignatureClock.tally model start vocabulary encoding law past more := by
  induction blocks generalizing past more with
  | zero => exact Nat.zero_le _
  | succ blocks ih =>
    have firstRoom : ForwardResponseClock.width model start ≤ more.length := by rw [Nat.mul_succ] at room; omega
    have first := a_pending_signature_forces_an_opportunity_in_the_next_actual_roster_block model start vocabulary encoding law
      past (more.take (ForwardResponseClock.width model start))
      (by simp only [List.length_take, Nat.min_eq_left firstRoom]; exact Nat.le_refl _)
      (by simpa only [List.take_zero, List.append_nil] using pending 0 (Nat.zero_le _))
      (SignatureClock.availability_at_an_actual_initial_segment model start vocabulary encoding law past more _ available)
    have rest := ih (past ++ more.take (ForwardResponseClock.width model start)) (more.drop (ForwardResponseClock.width model start))
      (by simp only [List.length_drop]; rw [Nat.mul_succ] at room; omega) (by
        intro n inside
        have index : ForwardResponseClock.width model start + n ≤ more.length := by
          simp only [List.length_drop] at inside; omega
        have cut : past ++ more.take (ForwardResponseClock.width model start + n) =
            (past ++ more.take (ForwardResponseClock.width model start)) ++ (more.drop (ForwardResponseClock.width model start)).take n := by
          rw [List.take_add, List.append_assoc]
        rw [← cut]
        exact pending _ index)
      (SignatureClock.availability_at_the_same_actual_remaining_segment model start vocabulary encoding law past more _ firstRoom available)
    have partition := SignatureClock.tally_append model start vocabulary encoding law past
      (more.take (ForwardResponseClock.width model start)) (more.drop (ForwardResponseClock.width model start))
    rw [List.take_append_drop] at partition
    omega

theorem actual_opportunity_budget_generates_a_common_clear_cut
    (past more : JointResponse.Stages model) (budget : Nat)
    (room : ForwardResponseClock.width model start * (budget + 1) ≤ more.length)
    (bounded : SignatureClock.tally model start vocabulary encoding law past more ≤ budget)
    (available : SignatureClock.Available model start vocabulary encoding law past more) :
    ∃ n ≤ ForwardResponseClock.width model start * (budget + 1),
      SignatureEligibility.Clear model start vocabulary encoding law (past ++ more.take n) := by
  by_contra noCut
  have pending : ∀ n ≤ (more.take (ForwardResponseClock.width model start * (budget + 1))).length,
      ¬ SignatureEligibility.Clear model start vocabulary encoding law (past ++ (more.take (ForwardResponseClock.width model start * (budget + 1))).take n) := by
    intro n inside clear
    have index : n ≤ ForwardResponseClock.width model start * (budget + 1) := by
      simp only [List.length_take, Nat.min_eq_left room] at inside; exact inside
    rw [List.take_take, Nat.min_eq_left index] at clear
    exact noCut ⟨n, index, clear⟩
  have lower := a_run_without_a_common_clear_cut_pays_once_per_actual_roster_block model start vocabulary encoding law
    past (more.take (ForwardResponseClock.width model start * (budget + 1))) (budget + 1)
    (by simp only [List.length_take, Nat.min_eq_left room]; exact Nat.le_refl _) pending
    (SignatureClock.availability_at_an_actual_initial_segment model start vocabulary encoding law past more _ available)
  have partition := SignatureClock.tally_append model start vocabulary encoding law past
    (more.take (ForwardResponseClock.width model start * (budget + 1))) (more.drop (ForwardResponseClock.width model start * (budget + 1)))
  rw [List.take_append_drop] at partition
  omega

theorem primitive_source_conditions_generate_a_live_common_signature_cut
    (past : JointResponse.Stages model) (delayAllowance : Nat)
    (reserve : ForwardResponseBudget.deadline model start vocabulary encoding law past + 1 ≤ JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delayAllowance
      (JointResponseRun.produce model start vocabulary encoding law past).stages)
    (available : SignatureClock.Available model start vocabulary encoding law past
      ((JointResponseRun.produce model start vocabulary encoding law past).stages.drop past.length)) :
    let full := (JointResponseRun.produce model start vocabulary encoding law past).stages
    ∃ n, past.length ≤ n ∧ n ≤ past.length + ForwardResponseBudget.deadline model start vocabulary encoding law past ∧
      n ≤ full.length ∧ SignatureEligibility.Clear model start vocabulary encoding law (full.take n) ∧
      0 < JointResponse.fuel model start (full.take n) := by
  dsimp only
  let full := (JointResponseRun.produce model start vocabulary encoding law past).stages
  let window := ForwardResponseBudget.deadline model start vocabulary encoding law past
  obtain ⟨more, exactFull⟩ := JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law
    (JointResponse.fuel model start past) past
  change past ++ more = full at exactFull
  have availability : SignatureClock.Available model start vocabulary encoding law past more := by
    change SignatureClock.Available model start vocabulary encoding law past (full.drop past.length) at available
    simpa only [← exactFull, List.drop_left] using available
  have cut : ∀ n, full.take (past.length + n) = past ++ more.take n := by
    intro n; rw [← exactFull]; simp [List.take_append]
  have someCut : ∃ n ≤ window, n ≤ more.length ∧ SignatureEligibility.Clear model start vocabulary encoding law (past ++ more.take n) := by
    by_cases room : window ≤ more.length
    · have upper := SignatureClock.the_original_source_bounds_all_signature_opportunities model start vocabulary encoding law
        (JointResponse.fuel model start past) past delayAllowance compliant
      unfold SignatureClock.physical at upper
      change SignatureClock.tally model start vocabulary encoding law past (full.drop past.length) ≤ _ at upper
      rw [← exactFull, List.drop_left] at upper
      obtain ⟨n, inside, clear⟩ := actual_opportunity_budget_generates_a_common_clear_cut model start vocabulary encoding law past more
        (ForwardResponseBudget.allowance model start vocabulary encoding law past) room upper availability
      change n ≤ window at inside
      exact ⟨n, inside, by omega, clear⟩
    · have live : JointResponse.fuel model start full ≠ 0 := by
        intro empty
        have fuel := UnifiedResponse.fuel_after_actual_extension model start past more
        change JointResponse.fuel model start (past ++ more) = JointResponse.fuel model start past - more.length at fuel
        rw [exactFull, empty] at fuel
        omega
      have result := JointResponseRun.source_budget_generates_complete_or_actual_exhaustion model start vocabulary encoding law past
      have complete : (JointResponseRun.produce model start vocabulary encoding law past).status = .jointComplete := by
        rcases result with complete | exhausted
        · exact complete
        · exact False.elim (live exhausted.2)
      have gates := (JointResponseRun.completion_has_both_source_generated_gates model start vocabulary encoding law
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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureWindow
