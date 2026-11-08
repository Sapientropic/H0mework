import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRunCost

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawServiceWindow
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

-- A half-open invocation window reads the actual audited raw-source admission gates.
-- Its premise contains no service receipt, terminal row or completion certificate.
def Available (blocks width : Nat) (past : JointResponse.Stages model) : Prop :=
  ∀ block < blocks,
    (UnifiedRecoveryRun.run model start vocabulary encoding law ((block + 1) * width) past).trace.length = (block + 1) * width →
    ∃ offset < width,
      (RawNativeService.produce model start
        (UnifiedRunPrefix.atCut model start vocabulary encoding law past (block * width + offset)) vocabulary encoding law).isSome = true

theorem one_raw_window_generates_an_actual_service
    (width : Nat) (past : JointResponse.Stages model)
    (available : ∃ offset < width,
      (RawNativeService.produce model start
        (UnifiedRunPrefix.atCut model start vocabulary encoding law past offset) vocabulary encoding law).isSome = true) :
    0 < (NativeServiceTrace.records model start vocabulary encoding law width past).length := by
  obtain ⟨offset, inside, present⟩ := available
  cases actual : RawNativeService.produce model start
      (UnifiedRunPrefix.atCut model start vocabulary encoding law past offset) vocabulary encoding law with
  | none => rw [actual] at present; cases present
  | some source =>
    obtain ⟨entry, member, same⟩ := RawNativeServiceForward.the_next_actual_source_visit_has_its_generated_service_record
      model start (UnifiedRunPrefix.atCut model start vocabulary encoding law past offset) vocabulary encoding law source (width - offset - 1)
    have tail : width - offset - 1 + 1 = width - offset := by omega
    rw [tail] at member
    have positive : 0 < (NativeServiceTrace.records model start vocabulary encoding law (width - offset)
        (UnifiedRunPrefix.atCut model start vocabulary encoding law past offset)).length := List.length_pos_of_mem member
    have compose := UnifiedRunPrefix.actual_service_records_compose model start vocabulary encoding law offset (width - offset) past
    rw [Nat.add_sub_of_le (Nat.le_of_lt inside)] at compose
    rw [compose, List.length_append]
    omega

theorem complete_actual_windows_pay_distinct_services
    (blocks width : Nat) (past : JointResponse.Stages model)
    (available : Available model start vocabulary encoding law blocks width past)
    (full : (UnifiedRecoveryRun.run model start vocabulary encoding law (blocks * width) past).trace.length = blocks * width) :
    blocks ≤ (NativeServiceTrace.records model start vocabulary encoding law (blocks * width) past).length := by
  induction blocks with
  | zero => exact Nat.zero_le _
  | succ blocks ih =>
    have oldFull := UnifiedRunPrefix.every_prefix_of_a_full_actual_trace_is_full model start vocabulary encoding law
      ((blocks + 1) * width) (blocks * width) past (Nat.mul_le_mul_right width (by omega)) full
    have oldAvailable : Available model start vocabulary encoding law blocks width past := by
      intro block inside
      exact available block (by omega)
    have old := ih oldAvailable oldFull
    have witness := available blocks (by omega) full
    have localWindow : ∃ offset < width,
        (RawNativeService.produce model start
          (UnifiedRunPrefix.atCut model start vocabulary encoding law
            (UnifiedRunPrefix.atCut model start vocabulary encoding law past (blocks * width)) offset) vocabulary encoding law).isSome = true := by
      obtain ⟨offset, inside, present⟩ := witness
      refine ⟨offset, inside, ?_⟩
      rw [← UnifiedRunPrefix.actual_run_prefixes_compose]
      exact present
    have paid := one_raw_window_generates_an_actual_service model start vocabulary encoding law width
      (UnifiedRunPrefix.atCut model start vocabulary encoding law past (blocks * width)) localWindow
    have compose := UnifiedRunPrefix.actual_service_records_compose model start vocabulary encoding law (blocks * width) width past
    rw [Nat.add_mul, Nat.one_mul, compose, List.length_append]
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawServiceWindow
