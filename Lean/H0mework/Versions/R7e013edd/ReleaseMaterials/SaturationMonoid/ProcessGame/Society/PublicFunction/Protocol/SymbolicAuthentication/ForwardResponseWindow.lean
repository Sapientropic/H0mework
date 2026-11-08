import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseWindow
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

-- A finite condition on primitive state at actual future cuts, without a Ready or ServedAt field.
def Available (past full : JointResponse.Stages model) : Prop :=
  ∀ n : Fin full.length, past.length ≤ n.val → ∀ receiver : Fin model.source.code.sites,
    Distributed.Recall.Information.Agency.ownerAt model.source.code
      (EventHistory.execute start (full.take n.val)).ownerStart
      (EventStep.seed (EventHistory.execute start (full.take n.val))).history.length = some receiver →
    ResponseEligibility.pendingAt model start vocabulary encoding law (full.take n.val) receiver ≠ [] →
    ResponseEligibility.Resources model start (full.take n.val) receiver

instance (past full : JointResponse.Stages model) : Decidable (Available model start vocabulary encoding law past full) := by
  unfold Available
  infer_instance

theorem actual_prefix_restricts_primitive_availability
    (past middle full : JointResponse.Stages model) (ordered : middle <+: full)
    (available : Available model start vocabulary encoding law past full) :
    Available model start vocabulary encoding law past middle := by
  intro n afterPast receiver owned pending
  obtain ⟨tail, same⟩ := ordered
  have cut : full.take n.val = middle.take n.val := by
    rw [← same, List.take_append, Nat.sub_eq_zero_of_le (by omega), List.take_zero, List.append_nil]
  have actual := available ⟨n.val, by have size := congrArg List.length same; simp only [List.length_append] at size; omega⟩ afterPast receiver
  rw [cut] at actual
  exact actual owned pending

theorem an_actual_unhandled_identity_has_local_pending_evidence
    (past : JointResponse.Stages model) (id : Fin model.source.code.sites × Nat)
    (born : id ∈ AdaptiveRejectionInventory.identities start vocabulary encoding law past)
    (unhandled : id ∉ handled model start vocabulary encoding law past) :
    ResponseEligibility.pendingAt model start vocabulary encoding law past id.1 ≠ [] := by
  obtain ⟨entry, observed, same⟩ :=
    (AdaptiveRejectionInventory.mem_identities start vocabulary encoding law past id.1 id.2).mp born
  have member : entry ∈ ResponseEligibility.pendingAt model start vocabulary encoding law past id.1 := by
    apply List.mem_filter.mpr
    refine ⟨observed, decide_eq_true ?_⟩
    intro registered
    apply unhandled
    apply List.mem_toFinset.mpr
    simpa only [same, Prod.mk.eta] using registered
  intro empty
  rw [empty] at member
  contradiction

theorem a_persistent_original_identity_forces_the_roster_opportunity_lower_bound
    (past more : JointResponse.Stages model) (id : Fin model.source.code.sites × Nat) (blocks : Nat)
    (room : ForwardResponseClock.width model start * blocks ≤ more.length)
    (born : id ∈ AdaptiveRejectionInventory.identities start vocabulary encoding law past)
    (unhandled : id ∉ handled model start vocabulary encoding law (past ++ more))
    (available : Available model start vocabulary encoding law past (past ++ more)) :
    blocks ≤ PhysicalOpportunityClock.tally model start vocabulary encoding law past more := by
  apply ForwardResponseClock.persistent_owned_cut_eligibility_generates_one_opportunity_per_source_roster_block
    model start vocabulary encoding law past more id.1 blocks room
  intro n inside owned
  have initial : past <+: past ++ more.take n := List.prefix_append _ _
  have finalCut : past ++ more.take n <+: past ++ more := by
    exact ⟨more.drop n, by rw [List.append_assoc, List.take_append_drop]⟩
  have pending := an_actual_unhandled_identity_has_local_pending_evidence model start vocabulary encoding law
    (past ++ more.take n) id
    (rejection_births_never_disappear model start vocabulary encoding law _ _ initial born)
    (fun registered => unhandled (handled_never_disappears model start vocabulary encoding law _ _ finalCut registered))
  have cut : (past ++ more).take (past.length + n) = past ++ more.take n := by simp [List.take_append]
  have resources := available ⟨past.length + n, by simp only [List.length_append]; omega⟩
    (by change past.length ≤ past.length + n; omega) id.1
  rw [cut] at resources
  have resource := resources owned pending
  simp only [ResponseEligibility.eligible, owned, Bool.and_eq_true_iff, decide_eq_true_eq]
  exact ⟨by simpa only [Bool.not_eq_true', List.isEmpty_eq_false_iff] using pending, resource⟩

theorem primitive_source_conditions_generate_a_forward_rejection_deadline
    (past : JointResponse.Stages model) (birthAllowance : Nat)
    (reserve : ForwardResponseBudget.deadline model start vocabulary encoding law past ≤ JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start birthAllowance
      (JointResponseRun.produce model start vocabulary encoding law past).stages)
    (births : RejectionService.BirthsWithin model start vocabulary encoding law
      (JointResponseRun.produce model start vocabulary encoding law past).stages past.length)
    (available : Available model start vocabulary encoding law past
      (JointResponseRun.produce model start vocabulary encoding law past).stages) :
    let full := (JointResponseRun.produce model start vocabulary encoding law past).stages
    let stop := past.length + ForwardResponseBudget.deadline model start vocabulary encoding law past
    UnifiedResponse.rejections model start vocabulary encoding law (full.take stop) = [] ∧
      UnifiedResponse.rejections model start vocabulary encoding law full = [] := by
  dsimp only
  let full := (JointResponseRun.produce model start vocabulary encoding law past).stages
  let window := ForwardResponseBudget.deadline model start vocabulary encoding law past
  have original := JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law
    (JointResponse.fuel model start past) past
  change past <+: full at original
  obtain ⟨more, exactFull⟩ := original
  have initialCut : full.take past.length = past := by rw [← exactFull]; simp
  have atStop : UnifiedResponse.rejections model start vocabulary encoding law (full.take (past.length + window)) = [] := by
    by_cases room : window ≤ more.length
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro id member
      obtain ⟨bornAtStop, unhandled⟩ := (unhandled_membership model start vocabulary encoding law _ id).mp member
      have born : id ∈ AdaptiveRejectionInventory.identities start vocabulary encoding law past := by
        rw [← initialCut]
        exact births (rejection_births_never_disappear model start vocabulary encoding law _ _ (List.take_prefix _ _) bornAtStop)
      have cut : full.take (past.length + window) = past ++ more.take window := by rw [← exactFull]; simp [List.take_append]
      rw [cut] at unhandled
      have prefixStop : past ++ more.take window <+: full := by
        rw [← cut]
        exact List.take_prefix _ _
      have lower := a_persistent_original_identity_forces_the_roster_opportunity_lower_bound
        model start vocabulary encoding law past (more.take window) id
        (ForwardResponseBudget.allowance model start vocabulary encoding law past + 1)
        (by simp only [List.length_take, Nat.min_eq_left room]; exact Nat.le_refl _) born unhandled
        (actual_prefix_restricts_primitive_availability model start vocabulary encoding law past _ full prefixStop available)
      have upper := ForwardResponseBudget.every_compliant_actual_run_has_a_source_generated_physical_opportunity_budget
        model start vocabulary encoding law (JointResponse.fuel model start past) past birthAllowance compliant
      have total : PhysicalOpportunityClock.physical model start vocabulary encoding law (JointResponse.fuel model start past) past =
          PhysicalOpportunityClock.tally model start vocabulary encoding law past more := by
        unfold PhysicalOpportunityClock.physical
        change PhysicalOpportunityClock.tally model start vocabulary encoding law past (full.drop past.length) = _
        rw [← exactFull, List.drop_left]
      have partition := PhysicalOpportunityClock.tally_append model start vocabulary encoding law past (more.take window) (more.drop window)
      rw [List.take_append_drop] at partition
      rw [total] at upper
      omega
    · have exhaustedImpossible : JointResponse.fuel model start full ≠ 0 := by
        intro exhausted
        have fuel := UnifiedResponse.fuel_after_actual_extension model start past more
        change JointResponse.fuel model start (past ++ more) = JointResponse.fuel model start past - more.length at fuel
        rw [exactFull, exhausted] at fuel
        omega
      have result := JointResponseRun.source_budget_generates_complete_or_actual_exhaustion model start vocabulary encoding law past
      have complete : (JointResponseRun.produce model start vocabulary encoding law past).status = .jointComplete := by
        rcases result with complete | exhausted
        · exact complete
        · exact False.elim (exhaustedImpossible exhausted.2)
      have cleared := (JointResponseRun.completion_has_both_source_generated_gates model start vocabulary encoding law
        (JointResponse.fuel model start past) past complete).1.2.1
      have length : full.length ≤ past.length + window := by
        have size := congrArg List.length exactFull
        simp only [List.length_append] at size
        omega
      rw [List.take_of_length_le length]
      exact cleared
  refine ⟨atStop, ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro id member
  obtain ⟨born, unhandled⟩ := (unhandled_membership model start vocabulary encoding law _ id).mp member
  have atInitial : id ∈ AdaptiveRejectionInventory.identities start vocabulary encoding law (full.take past.length) := births born
  have atDeadline := rejection_births_never_disappear model start vocabulary encoding law _ _
    (List.take_prefix_take_left (show past.length ≤ past.length + window by omega)) atInitial
  have registered : id ∈ handled model start vocabulary encoding law (full.take (past.length + window)) := by
    by_contra absent
    have pending := (unhandled_membership model start vocabulary encoding law _ id).mpr ⟨atDeadline, absent⟩
    rw [atStop] at pending
    contradiction
  exact unhandled (handled_never_disappears model start vocabulary encoding law _ _ (List.take_prefix _ _) registered)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseWindow
