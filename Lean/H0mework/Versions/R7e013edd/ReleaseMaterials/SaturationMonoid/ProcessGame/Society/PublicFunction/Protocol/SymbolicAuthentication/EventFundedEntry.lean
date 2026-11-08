import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AuthorityEventFunding

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventFundedEntry
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
abbrev blocks := PersistentDutyEntry.blocks model start vocabulary encoding law
abbrev deadline := PersistentDutyEntry.deadline model start vocabulary encoding law

def initialMemory (past : JointResponse.Stages model) : Bool :=
  (List.finRange model.source.code.sites).all fun site =>
    model.source.code.memoryReady ((EventStep.seed (EventHistory.execute start past)).frame.inbox site)

def check (past : JointResponse.Stages model) : Bool :=
  SourceSignatureInterface.inspect model && SourceReadyMemory.inspect model.source.code &&
    initialMemory model start past && decide (RejectionResponse.Active model start past) &&
    AuthorityEventFunding.inspect (EventHistory.execute start past)
      ((atCut model start vocabulary encoding law past (deadline model start vocabulary encoding law past)).drop past.length)

theorem source_interfaces_and_actual_events_generate_primitive_availability
    (past tail : JointResponse.Stages model)
    (interface : SourceSignatureInterface.inspect model = true)
    (memory : SourceReadyMemory.inspect model.source.code = true)
    (initial : initialMemory model start past = true)
    (active : RejectionResponse.Active model start past)
    (effects : AuthorityEventFunding.inspect (EventHistory.execute start past) tail = true)
    (room : tail.length ≤ JointResponse.fuel model start past) :
    SignatureClock.Available model start vocabulary encoding law past tail := by
  have closure := SourceReadyMemory.the_finite_source_interface_generates_ready_memory_closure memory
  intro n receiver _ _
  have memoryBefore := (List.all_eq_true.mp initial) receiver (List.mem_finRange _)
  have memoryAfter := SourceReadyMemory.the_actual_history_preserves_ready_memory closure
    (EventHistory.execute start past) (tail.take n.val) receiver memoryBefore
  rw [← OriginQueue.execute_append] at memoryAfter
  have authority := AuthorityEventFunding.actual_effects_generate_authority_at_every_required_physical_cut
    (EventHistory.execute start past) tail active effects n.val n.isLt
  rw [← OriginQueue.execute_append] at authority
  have static := SourceSignatureInterface.checked_interface_generates_static_and_legal_signature_resources
    model interface (EventStep.seed (EventHistory.execute start (past ++ tail.take n.val))).current receiver
  have fuel := UnifiedResponse.fuel_after_actual_extension model start past (tail.take n.val)
  have taken : (tail.take n.val).length = n.val := by simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt n.isLt)]
  change JointResponse.fuel model start (past ++ tail.take n.val) = JointResponse.fuel model start past - (tail.take n.val).length at fuel
  rw [taken] at fuel
  exact ⟨static.1, static.2.1, static.2.2.1, by omega, memoryAfter, static.2.2.2.1, static.2.2.2.2, authority⟩

theorem availability_restricts_to_the_same_actual_interval
    (past middle later full : JointResponse.Stages model)
    (first : past <+: middle) (second : middle <+: later) (third : later <+: full)
    (available : SignatureClock.Available model start vocabulary encoding law past (full.drop past.length)) :
    SignatureClock.Available model start vocabulary encoding law middle (later.drop middle.length) := by
  obtain ⟨left, rfl⟩ := first
  obtain ⟨right, rfl⟩ := second
  obtain ⟨rest, rfl⟩ := third
  have whole : SignatureClock.Available model start vocabulary encoding law past (left ++ (right ++ rest)) := by
    simpa only [List.append_assoc, List.drop_left] using available
  have remaining := SignatureClock.availability_at_the_same_actual_remaining_segment model start vocabulary encoding law
    past (left ++ (right ++ rest)) left.length (by simp) whole
  have afterLeft : SignatureClock.Available model start vocabulary encoding law (past ++ left) (right ++ rest) := by
    simpa only [List.take_left, List.drop_left] using remaining
  have shorter := SignatureClock.availability_at_an_actual_initial_segment model start vocabulary encoding law
    (past ++ left) (right ++ rest) right.length afterLeft
  simpa only [List.take_left, List.drop_left] using shorter

theorem source_events_generate_all_original_resource_windows
    (past : JointResponse.Stages model) (checked : check model start vocabulary encoding law past = true)
    (reserve : deadline model start vocabulary encoding law past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past) :
    PersistentDutyEntry.resources model start vocabulary encoding law (blocks model start vocabulary encoding law past) past = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨⟨interface, memory⟩, initial⟩, active⟩, effects⟩
  let full := atCut model start vocabulary encoding law past (deadline model start vocabulary encoding law past)
  obtain ⟨tail, actual⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law
    (deadline model start vocabulary encoding law past) past
  change past ++ tail = full at actual
  have physical := UnifiedRunCost.actual_invocations_pay_all_physical_stages model start vocabulary encoding law
    (deadline model start vocabulary encoding law past) past
  change full.length ≤ _ at physical
  have room : tail.length ≤ JointResponse.fuel model start past := by
    rw [← actual, List.length_append] at physical
    omega
  have available := source_interfaces_and_actual_events_generate_primitive_availability model start vocabulary encoding law
    past (full.drop past.length) interface memory initial active effects (by rw [← actual, List.drop_left]; exact room)
  apply List.all_eq_true.mpr
  intro n inside
  have bound : (n + 1) * PersistentDutyEntry.width model start ≤ deadline model start vocabulary encoding law past :=
    Nat.mul_le_mul_right _ (List.mem_range.mp inside)
  have beginBound : n * PersistentDutyEntry.width model start ≤ (n + 1) * PersistentDutyEntry.width model start := Nat.mul_le_mul_right _ (Nat.le_succ n)
  have interval := availability_restricts_to_the_same_actual_interval model start vocabulary encoding law past
    (atCut model start vocabulary encoding law past (n * PersistentDutyEntry.width model start))
    (atCut model start vocabulary encoding law past ((n + 1) * PersistentDutyEntry.width model start)) full
    (UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law _ past)
    (FundedSignatureEntry.actual_cut_is_a_prefix_of_every_later_cut model start vocabulary encoding law past _ _ beginBound)
    (FundedSignatureEntry.actual_cut_is_a_prefix_of_every_later_cut model start vocabulary encoding law past _ _ bound) available
  have compose : atCut model start vocabulary encoding law past ((n + 1) * PersistentDutyEntry.width model start) =
      atCut model start vocabulary encoding law (atCut model start vocabulary encoding law past (n * PersistentDutyEntry.width model start)) (PersistentDutyEntry.width model start) := by
    rw [Nat.add_mul, Nat.one_mul]
    exact UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law _ _ past
  rw [compose] at interval
  exact decide_eq_true interval

theorem initial_confirmation_and_actual_source_events_generate_the_original_entry
    (past : JointResponse.Stages model) (delay : Nat)
    (initial : UnifiedResponse.duties model start vocabulary encoding law past = [])
    (checked : check model start vocabulary encoding law past = true)
    (reserve : deadline model start vocabulary encoding law past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (atCut model start vocabulary encoding law past (deadline model start vocabulary encoding law past))) :
    ∃ index,
      CommunicationProgressSource.locate model start vocabulary encoding law
        (CommunicationProgressSource.horizon model start vocabulary encoding law past) past = some index ∧
      index ≤ CommunicationProgressSource.horizon model start vocabulary encoding law past ∧
      CommunicationProgressSource.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past index) :=
  PersistentDutyEntry.initial_confirmation_and_primitive_resources_generate_the_original_entry model start vocabulary encoding law past delay
    initial (source_events_generate_all_original_resource_windows model start vocabulary encoding law past checked reserve) reserve compliant

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventFundedEntry
