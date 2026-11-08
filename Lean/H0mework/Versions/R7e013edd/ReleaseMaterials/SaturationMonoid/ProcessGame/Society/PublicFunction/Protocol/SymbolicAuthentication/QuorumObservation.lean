import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EnvelopeObservation
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualAdaptiveWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QuorumObservation
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
  (first second : List (EventHistory.Stage (code := code)))
  (same : EnvelopeObservation.Related (StageTrace.records start first) (StageTrace.records start second))

include same in
theorem source_admission_equal (scope : Scope) :
    StageSourceAdmission.check start vocabulary first scope = StageSourceAdmission.check start vocabulary second scope := by
  have allEqual {left right : List (StageTrace.Record (code := code))} (related : EnvelopeObservation.Related left right) :
      (left.all fun row => SourceCapabilityAdmission.check start.source vocabulary row.protocol scope) =
        (right.all fun row => SourceCapabilityAdmission.check start.source vocabulary row.protocol scope) := by
    induction related with
    | nil => rfl
    | cons item rest ih => simp only [List.all_cons,item.protocol,ih]
  exact allEqual same

include same in
theorem count_equal : first.length = second.length := by
  rw [← StageTrace.record_count start first,← StageTrace.record_count start second]
  exact same.length_eq

include same in
theorem ready_at_equal (receiver : Fin code.sites) (index : Nat) :
    StageQueueProgress.readyAt vocabulary encoding law start first receiver index =
      StageQueueProgress.readyAt vocabulary encoding law start second receiver index := by
  have rows := EnvelopeObservation.communication same
  unfold StageQueueProgress.readyAt
  rw [CommunicationObservation.incoming_equal vocabulary encoding start start first second rows index]
  by_cases bounded : index < (StageTrace.records start first).length
  · have other : index < (StageTrace.records start second).length := by rw [← rows.length_eq];exact bounded
    simp only [List.getElem?_eq_getElem bounded,List.getElem?_eq_getElem other]
    cases StageReception.incoming vocabulary encoding start second index with
    | none => rfl
    | some wire =>
      dsimp only
      have checked : StageReception.check vocabulary encoding law start first receiver ((StageTrace.records start first)[index]'bounded) [] wire =
          StageReception.check vocabulary encoding law start second receiver ((StageTrace.records start second)[index]'other) [] wire := by
        simpa only [List.get_eq_getElem] using
          CommunicationObservation.check_equal vocabulary encoding start start first second rows law receiver (rows.get bounded other) [] wire
      rw [checked]
  · have other : ¬ index < (StageTrace.records start second).length := by rw [← rows.length_eq];exact bounded
    rw [List.getElem?_eq_none_iff.mpr (by omega),List.getElem?_eq_none_iff.mpr (by omega)]

include same in
theorem ready_support_equal (receiver : Fin code.sites) (scope : Scope) (value : Bool) :
    StageQueueProgress.readySupport vocabulary encoding law start first receiver scope value =
      StageQueueProgress.readySupport vocabulary encoding law start second receiver scope value := by
  unfold StageQueueProgress.readySupport
  rw [count_equal start first second same]
  congr 1
  apply List.filterMap_congr
  intro index _
  simp only [StageQueueProgress.supportingAt,ready_at_equal start vocabulary encoding law first second same receiver index]

include same in
theorem original_quorum_plan_equal (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) :
    AdmittedAdaptiveWindow.plan start vocabulary encoding law first receiver scope threshold =
      AdmittedAdaptiveWindow.plan start vocabulary encoding law second receiver scope threshold := by
  simp only [AdmittedAdaptiveWindow.plan,source_admission_equal start vocabulary first second same scope,
    ready_support_equal start vocabulary encoding law first second same receiver scope]

include same in
theorem original_admitted_decision_equal (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) :
    AdmittedStageQuorum.produce start vocabulary encoding law first receiver scope threshold =
      AdmittedStageQuorum.produce start vocabulary encoding law second receiver scope threshold := by
  have reception := CommunicationObservation.run_equal vocabulary encoding start start first second
    (EnvelopeObservation.communication same) law receiver second.length
  simp only [AdmittedStageQuorum.produce,source_admission_equal start vocabulary first second same scope,
    AdmittedStageQuorum.observed,count_equal start first second same,reception]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QuorumObservation
