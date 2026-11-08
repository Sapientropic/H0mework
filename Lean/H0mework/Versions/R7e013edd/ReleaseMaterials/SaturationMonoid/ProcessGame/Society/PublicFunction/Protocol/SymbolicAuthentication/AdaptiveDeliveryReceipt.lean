import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryReceipt
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace AdaptiveDeliveryDeadline

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

-- These are original wire/payment/scope/timing checks with an empty seen set;
-- neither an existing receipt nor a certificate is an input.
abbrev ReadyWithin (allowance birth serial : Nat) (receiver : Fin code.sites) :=
  ∀ index, birth ≤ index → index < horizon start allowance birth →
    StageReception.delivered (row start protocols rivals index) serial = true →
    ∃ wire, StageQueueProgress.readyAt vocabulary encoding law start
      (stages protocols rivals (horizon start allowance birth)) receiver index = some wire

theorem source_ready_communication_generates_a_bounded_authenticated_receipt
    (allowance birth serial : Nat) (receiver : Fin code.sites)
    (enough : horizon start allowance birth ≤ (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals birth).frame.sent.length)
    (untried : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals birth).past)
    (compliant : Compliant start protocols rivals allowance (horizon start allowance birth))
    (ready : ReadyWithin vocabulary encoding law start protocols rivals allowance birth serial receiver) :
    (∀ n ≤ horizon start allowance birth, InterferenceEnvelope.spent start (stages protocols rivals n) ≤ code.eventLimit) ∧
    ∃ index wire, birth ≤ index ∧ index < horizon start allowance birth ∧
      StageReception.delivered (row start protocols rivals index) serial = true ∧
      StageQueueProgress.readyAt vocabulary encoding law start (stages protocols rivals (horizon start allowance birth)) receiver index = some wire ∧
      ∃ receipt ∈ (StageReception.run vocabulary encoding law start
        (stages protocols rivals (horizon start allowance birth)) receiver (index + 1)).receipts,
        receipt.wire.ballot = wire.ballot := by
  refine ⟨AdaptiveDeliveryBudget.every_actual_prefix_keeps_the_one_source_interface_budget
    start protocols rivals allowance (horizon start allowance birth) compliant, ?_⟩
  obtain ⟨index, born, bounded, delivered⟩ :=
    every_compliant_adaptive_execution_attempts_each_pending_packet_before_the_source_deadline
      start protocols rivals allowance birth serial enough present untried compliant
  obtain ⟨wire, checked⟩ := ready index born bounded delivered
  exact ⟨index, wire, born, bounded, delivered, checked,
    StageQueueProgress.source_ready_delivery_generates_or_preserves_its_actual_content_receipt
      vocabulary encoding law start (stages protocols rivals (horizon start allowance birth)) receiver index wire checked⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryReceipt
