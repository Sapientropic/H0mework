import H0mework.Realization.SourceComparison.GroundedRealization
import H0mework.Physics.RootRuntime.RecoveryConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GroundedRealization

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CausalCore GroundedFaithfulRealization
open Stage9C.Revision StageNineHolonomicField StageNineCClassicalWorldAcceptance
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open DiracExteriorMatterAction

noncomputable section

abbrev World := SpinPair.livingRoot.toAnswerNextCausalWorld

def configuration {process : Process World} (faithful : FaithfulRealization World process)
    (visit : Recognition.Visit) (event : process.EventAt (ULift.up visit)) : StageNineHolonomicConfiguration :=
  match (recover faithful visit event).projectionOutcome (.inherited .configuration) with
  | .inl ⟨_, value⟩ => value
  | .inr impossible => nomatch impossible

theorem configuration_original {process : Process World} (faithful : FaithfulRealization World process)
    (visit : Recognition.Visit) (event : process.EventAt (ULift.up visit)) :
    configuration faithful visit event = Recognition.wholeField visit.current := rfl

theorem compiled_writer {process : Process World} (faithful : FaithfulRealization World process)
    (visit : Recognition.Visit) (event : process.EventAt (ULift.up visit)) :
    (process.compile event).generated = recover faithful visit event :=
  (recover_eq_generated faithful visit event).symm

theorem whole_ledger {process : Process World} (faithful : FaithfulRealization World process)
    (visit : Recognition.Visit) (event : process.EventAt (ULift.up visit)) :
    HEq (recover faithful visit event).wholeLedgerWriteBack
      (SpinPair.generatedEvolution (recover faithful visit event).occurrence) :=
  (recover faithful visit event).wholeLedgerWriteBack_eq

theorem accepted_configuration {process : Process World} (faithful : FaithfulRealization World process)
    (event : process.EventAt (ULift.up Runtime.visit)) :
    ClassicalWorldAcceptance Runtime.source (configuration faithful Runtime.visit event) := by
  rw [configuration_original]
  exact Recovery.stageOneThroughTenClosure.final.classical

theorem same_matter {process : Process World} (faithful : FaithfulRealization World process)
    (event : process.EventAt (ULift.up Runtime.visit)) :
    Recovery.MatterRecovery (configuration faithful Runtime.visit event) Recovery.stageEight := by
  rw [configuration_original]
  exact Recovery.stageOneThroughTenClosure.currentMatter

theorem quantum_read {process : Process World} (faithful : FaithfulRealization World process)
    (event : process.EventAt (ULift.up Runtime.visit)) :
    Stage9DEF.Source.restrict (configuration faithful Runtime.visit event) = Runtime.tick.answer := by
  rw [configuration_original]
  exact Runtime.tick_answer.symm

theorem whole_matter_action {process : Process World} (faithful : FaithfulRealization World process)
    (event : process.EventAt (ULift.up Runtime.visit))
    (point : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    (configuration faithful Runtime.visit event).conjugateMatter point
        (action ((configuration faithful Runtime.visit event).matter point)) =
      4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
        Stage9DEF.State.vectorEvaluation (Runtime.tick.answer point) (Stage9DEF.Compatibility.responseMatrix action) := by
  have original : configuration faithful Runtime.visit event = Stage9C.Material.SpinPair.actual :=
    (configuration_original faithful Runtime.visit event).trans Runtime.configuration_eq
  rw [original, Runtime.tick_vector]
  exact Stage9DEF.Compatibility.actual_action_quantumResponse point action

theorem actual_next (process : Process World) (event : process.EventAt (ULift.up Runtime.visit)) :
    (process.compile event).nextCurrent = Runtime.answerAndNext.nextCurrent :=
  Recovery.stageOneThroughTenClosure.final.activation.answerNext.symm

theorem actual_macro_next (process : Process World) (event : process.EventAt (ULift.up Runtime.visit)) :
    Runtime.tick.next.node.erase = ⟨MaterialN, (process.compile event).nextCurrent⟩ := by
  rw [actual_next]
  exact Recovery.stageOneThroughTenClosure.final.activation.macroAnswerNext

theorem source_realization_consumed :
    ∃ (process : Process World) (faithful : FaithfulRealization World process),
      (∀ left right : Recognition.Visit,
        TotalReality.InternallyDeterminedAt
          (RootTotalReality.semantics SpinPair.livingRoot.toAuthoritativeRoot) (left, right) ↔
        representedVisit process left ≠ representedVisit process right) ∧
      (∀ (other : Process World) (_otherFaithful : FaithfulRealization World other),
        ∃ generated : ProcessCommutingPresentation process other,
          ∀ candidate : ProcessCommutingPresentation process other,
          ∀ current event, (candidate.eventPresentation current).toFun event =
            (generated.eventPresentation current).toFun event) ∧
      (∀ visit event projection,
        HEq ((recover faithful visit event).projectionOutcome projection)
          (SpinPair.authoritativeRoot.projectionOutcomeAt projection visit.current)) ∧
      (∀ visit event, (process.compile event).generated = recover faithful visit event) ∧
      (∀ visit event, HEq (recover faithful visit event).wholeLedgerWriteBack
        (SpinPair.generatedEvolution (recover faithful visit event).occurrence)) ∧
      (∀ event : process.EventAt (ULift.up Runtime.visit),
        ClassicalWorldAcceptance Runtime.source (configuration faithful Runtime.visit event) ∧
        Recovery.MatterRecovery (configuration faithful Runtime.visit event) Recovery.stageEight ∧
        Stage9DEF.Source.restrict (configuration faithful Runtime.visit event) = Runtime.tick.answer ∧
        (∀ point action,
          (configuration faithful Runtime.visit event).conjugateMatter point
              (action ((configuration faithful Runtime.visit event).matter point)) =
            4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
              Stage9DEF.State.vectorEvaluation (Runtime.tick.answer point)
                (Stage9DEF.Compatibility.responseMatrix action)) ∧
        Runtime.tick.next.node.erase = ⟨MaterialN, (process.compile event).nextCurrent⟩) := by
  rcases source_generates_faithful_realization SpinPair.livingRoot with ⟨process, faithful⟩
  refine ⟨process, faithful, grounded_iff_represented_difference process,
    fun _ otherFaithful => source_generates_unique_comparison faithful otherFaithful,
    recovered_projection faithful, compiled_writer faithful, whole_ledger faithful, ?_⟩
  intro event
  exact ⟨accepted_configuration faithful event, same_matter faithful event, quantum_read faithful event,
    whole_matter_action faithful event, actual_macro_next process event⟩

end
end SaturationMonoid.PhysicsCore.Stage10.GroundedRealization
