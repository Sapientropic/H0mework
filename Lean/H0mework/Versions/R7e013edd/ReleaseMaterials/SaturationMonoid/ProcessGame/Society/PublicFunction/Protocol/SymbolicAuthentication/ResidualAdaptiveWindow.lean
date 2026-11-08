import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualAdaptiveDeadline
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedAdaptiveWindow
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryEffect

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualAdaptiveWindow
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace ResidualAdaptiveDeadline

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

abbrev full (begin allowance birth : Nat) := stages protocols rivals (horizon start protocols rivals begin allowance birth)
def timing (begin allowance birth : Nat) : Bool :=
  (List.range (horizon start protocols rivals begin allowance birth)).all fun n =>
    decide (begin ≤ n → InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) ∈
      InterferenceEnvelope.choices start (stages protocols rivals n) allowance)

theorem timing_iff (begin allowance birth : Nat) :
    timing start protocols rivals begin allowance birth = true ↔
      Compliant start protocols rivals begin allowance (horizon start protocols rivals begin allowance birth) := by
  simp only [timing,List.all_eq_true,List.mem_range,decide_eq_true_eq,Compliant]
  constructor <;> intro checked n first last
  · exact checked n last first
  · exact checked n last first

-- Past attempts and overspending remain attached to the original origin.
inductive Obstruction where
  | invalidBoundary | insufficientCuts | priorInterfaceViolation | communicationViolation
  | quorum (reason : AdmittedAdaptiveWindow.Obstruction)
  deriving DecidableEq
inductive Result where
  | blocked (reason : Obstruction)
  | ready (value : Bool)
  deriving DecidableEq

variable
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

def produce (begin allowance birth : Nat) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : Result :=
  if ¬ begin ≤ birth then .blocked .invalidBoundary
  else if ¬ horizon start protocols rivals begin allowance birth ≤ (EventStep.seed start).remaining then .blocked .insufficientCuts
  else if ¬ InterferenceEnvelope.spent start (stages protocols rivals begin) ≤ code.eventLimit then .blocked .priorInterfaceViolation
  else if timing start protocols rivals begin allowance birth ≠ true then .blocked .communicationViolation
  else match AdmittedAdaptiveWindow.plan start vocabulary encoding law (full start protocols rivals begin allowance birth) receiver scope threshold with
    | .blocked reason => .blocked (.quorum reason)
    | .ready value => .ready value

theorem generated_window_retains_the_one_source_budget_and_decides
    (begin allowance birth : Nat) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (ready : produce start protocols rivals vocabulary encoding law begin allowance birth receiver scope threshold = .ready value) :
    begin ≤ birth ∧ horizon start protocols rivals begin allowance birth ≤ (EventStep.seed start).remaining ∧
      Compliant start protocols rivals begin allowance (horizon start protocols rivals begin allowance birth) ∧
      (∀ n, begin ≤ n → n ≤ horizon start protocols rivals begin allowance birth →
        InterferenceEnvelope.spent start (stages protocols rivals n) ≤ code.eventLimit) ∧
      AdmittedStageQuorum.produce start vocabulary encoding law (full start protocols rivals begin allowance birth) receiver scope threshold = .decided value := by
  unfold produce at ready
  split at ready <;> try contradiction
  rename_i begun
  split at ready <;> try contradiction
  rename_i enough
  split at ready <;> try contradiction
  rename_i prior
  split at ready <;> try contradiction
  rename_i communication
  have chosen := (timing_iff start protocols rivals begin allowance birth).mp (of_not_not communication)
  have budget := continuation_preserves_the_actual_prefix_interface_spending start protocols rivals begin allowance _ chosen
  refine ⟨of_not_not begun,of_not_not enough,chosen,?_,?_⟩
  · intro n first last
    have bound := budget n first last
    have old := of_not_not prior
    omega
  · cases planned : AdmittedAdaptiveWindow.plan start vocabulary encoding law
      (full start protocols rivals begin allowance birth) receiver scope threshold with
    | blocked reason => simp only [planned] at ready; contradiction
    | ready choice =>
      simp only [planned] at ready
      cases Result.ready.inj ready
      exact AdmittedAdaptiveWindow.primitive_ready_support_generates_the_actual_source_admitted_decision
        start vocabulary encoding law _ receiver scope threshold value planned

omit vocabulary encoding law in
theorem bounded_delivery_generates_the_original_payment_disposition
    (begin allowance birth serial : Nat) (packet : code.Packet)
    (begun : begin ≤ birth)
    (enough : horizon start protocols rivals begin allowance birth ≤ (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals birth).frame.sent.length)
    (original : (state start protocols rivals birth).frame.sent[serial]? = some packet)
    (pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals birth).past)
    (interface : QueueMemoryEffect.restores packet = true)
    (compliant : Compliant start protocols rivals begin allowance (horizon start protocols rivals begin allowance birth)) :
    ∃ index, birth ≤ index ∧ index < horizon start protocols rivals begin allowance birth ∧
      StageReception.delivered (row start protocols rivals index) serial = true ∧
      (row start protocols rivals index).before.frame.sent[serial]? = some packet ∧
      QueueMemoryEffect.Resolution (row start protocols rivals index) serial packet := by
  obtain ⟨index,born,bounded,delivered⟩ := every_source_pending_packet_is_attempted_before_the_residual_deadline
    start protocols rivals begin allowance birth serial begun enough present pending compliant
  obtain ⟨more,same⟩ := (memory_queue start protocols rivals birth index born).2
  have packetAt : (row start protocols rivals index).before.frame.sent[serial]? = some packet := by
    change (state start protocols rivals index).frame.sent[serial]? = some packet
    rw [← same,List.getElem?_append,if_pos present]
    exact original
  exact ⟨index,born,bounded,delivered,packetAt,
    QueueMemoryEffect.the_actual_delivery_generates_recovery_or_its_exact_payment_obstruction
      (cursorAt start protocols rivals index) (protocols index,rivals index) serial packet packetAt delivered interface⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualAdaptiveWindow
