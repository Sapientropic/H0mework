import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedStageQuorum
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryReceipt

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedAdaptiveWindow
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

inductive Obstruction where
  | insufficientCuts | communicationViolation | unadmittedCapability | unsafeSourceBudget | insufficientReadySupport
  deriving DecidableEq
inductive Plan where
  | blocked (reason : Obstruction)
  | ready (value : Bool)
  deriving DecidableEq

def plan (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : Plan :=
  if StageSourceAdmission.check start vocabulary stages scope ≠ true then .blocked .unadmittedCapability
  else if ¬ code.sites + StageSourceAdmission.budget start vocabulary scope < threshold + threshold then .blocked .unsafeSourceBudget
  else match [false,true].find? (fun value => decide
      (threshold ≤ (StageQueueProgress.readySupport vocabulary encoding law start stages receiver scope value).card)) with
    | none => .blocked .insufficientReadySupport
    | some value => .ready value

theorem primitive_ready_support_generates_the_actual_source_admitted_decision
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (ready : plan start vocabulary encoding law stages receiver scope threshold = .ready value) :
    AdmittedStageQuorum.produce start vocabulary encoding law stages receiver scope threshold = .decided value := by
  unfold plan at ready
  split at ready <;> try contradiction
  rename_i admitted
  split at ready <;> try contradiction
  rename_i safe
  split at ready <;> try contradiction
  rename_i choice found
  cases Plan.ready.inj ready
  have accepted := of_not_not admitted
  have budget := of_not_not safe
  have positive : 0 < threshold := by omega
  have enough := of_decide_eq_true (List.find?_some (p := fun value => decide
    (threshold ≤ (StageQueueProgress.readySupport vocabulary encoding law start stages receiver scope value).card)) found)
  have actual := le_trans enough (Finset.card_le_card
    (StageQueueProgress.generated_support_is_in_the_actual_receiver vocabulary encoding law start stages receiver scope value))
  have existsDecision : ∃ choice, StageQuorum.readout (AdmittedStageQuorum.observed start vocabulary encoding law stages receiver) scope threshold = .decided choice := by
    unfold StageQuorum.readout
    rw [if_neg (by omega)]
    cases chosen : [false,true].find? (fun choice => decide (threshold ≤ (StageQuorum.support
        (AdmittedStageQuorum.observed start vocabulary encoding law stages receiver) scope choice).card)) with
    | some choice => exact ⟨choice,rfl⟩
    | none =>
      have absent := List.find?_eq_none.mp chosen value (by cases value <;> simp)
      exact False.elim (absent (decide_eq_true actual))
  obtain ⟨choice,decided⟩ := existsDecision
  have same := AdmittedStageQuorum.supported_values_agree start vocabulary encoding law stages stages receiver receiver scope threshold choice value
    accepted accepted (StageQuorum.decided_has_positive_quorum _ scope threshold choice decided).2 actual budget
  unfold AdmittedStageQuorum.produce
  rw [if_neg (not_not_intro accepted),if_neg (not_not_intro budget)]
  rw [decided,same]

variable (protocols : Nat → Rule code) (rivals : Nat → Opponent code)
abbrev deadline (allowance birth : Nat) := AdaptiveDeliveryDeadline.horizon start allowance birth
abbrev full (allowance birth : Nat) := AdaptiveDeliveryTrace.stages protocols rivals (deadline start allowance birth)

def timing (allowance birth : Nat) : Bool := (List.range (deadline start allowance birth)).all fun n => decide
  (InterferenceEnvelope.intake (AdaptiveDeliveryTrace.cursorAt start protocols rivals n) (rivals n) ∈
    InterferenceEnvelope.choices start (AdaptiveDeliveryTrace.stages protocols rivals n) allowance)

theorem timing_iff (allowance birth : Nat) : timing start protocols rivals allowance birth = true ↔
    AdaptiveDeliveryDeadline.Compliant start protocols rivals allowance (deadline start allowance birth) := by
  simp only [timing,List.all_eq_true,List.mem_range,decide_eq_true_eq,AdaptiveDeliveryDeadline.Compliant]

def windowPlan (allowance birth : Nat) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : Plan :=
  if ¬ deadline start allowance birth ≤ (EventStep.seed start).remaining then .blocked .insufficientCuts
  else if timing start protocols rivals allowance birth ≠ true then .blocked .communicationViolation
  else plan start vocabulary encoding law (full start protocols rivals allowance birth) receiver scope threshold

theorem generated_ready_window_decides_at_its_actual_source_deadline
    (allowance birth : Nat) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (ready : windowPlan start vocabulary encoding law protocols rivals allowance birth receiver scope threshold = .ready value) :
    deadline start allowance birth ≤ (EventStep.seed start).remaining ∧
      AdaptiveDeliveryDeadline.Compliant start protocols rivals allowance (deadline start allowance birth) ∧
      (∀ n ≤ deadline start allowance birth, InterferenceEnvelope.spent start (AdaptiveDeliveryTrace.stages protocols rivals n) ≤ code.eventLimit) ∧
      AdmittedStageQuorum.produce start vocabulary encoding law (full start protocols rivals allowance birth) receiver scope threshold = .decided value := by
  unfold windowPlan at ready
  split at ready <;> try contradiction
  rename_i enough
  split at ready <;> try contradiction
  rename_i compliant
  have actual := (timing_iff start protocols rivals allowance birth).mp (of_not_not compliant)
  exact ⟨of_not_not enough,actual,
    AdaptiveDeliveryBudget.every_actual_prefix_keeps_the_one_source_interface_budget start protocols rivals allowance (deadline start allowance birth) actual,
    primitive_ready_support_generates_the_actual_source_admitted_decision start vocabulary encoding law _ receiver scope threshold value ready⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedAdaptiveWindow
