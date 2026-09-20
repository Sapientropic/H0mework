import H0mework.Realization.SourceComparison.RawConsumption
import H0mework.Physics.MotherSource.GroundedRealization

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.RawSourceRealization

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision StageNineHolonomicField StageNineCClassicalWorldAcceptance
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open DiracExteriorMatterAction

noncomputable section

/-- Only the original lower event algebra generates this input. -/
def dynamics : RawGeneratedRoot.Dynamics where
  State := SpinPair.Current
  EventAt := SpinPair.source.toRootSource.actual.OccurrenceAt
  initial := SpinPair.source.initial
  emit := SpinPair.emitted
  update := fun occurrence => match SpinPair.source.toRootSource.actual.compile occurrence with
    | .nativeWrite action => SpinPair.V.nativeTarget action
    | .relationWrite impossible => nomatch impossible
    | .continuedTransport impossible => nomatch impossible
    | .borromeanRedirect impossible => nomatch impossible
    | .faithfulTerminal impossible => nomatch impossible

abbrev representedRoot := RawGeneratedRoot.root dynamics

def restore {state : SpinPair.Current}
    (event : representedRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt state) :=
  (RawGeneratedRoot.eventPresentation dynamics state).backward event

theorem original_history (index : Nat) :
    RawGeneratedRoot.currentAt dynamics index = (SpinPair.visit index).current := by
  induction index with
  | zero => rfl
  | succ index prior =>
    change SpinPair.next (RawGeneratedRoot.currentAt dynamics index) = SpinPair.next (SpinPair.visit index).current
    rw [prior]

theorem represented_history (index : Nat) :
    (RawGeneratedRoot.visitAt dynamics index).current = (SpinPair.visit index).current :=
  (RawGeneratedRoot.visit_current dynamics index).trans (original_history index)

def event : representedRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    Runtime.visit.current :=
  (represented_history 10) ▸
    (representedRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (RawGeneratedRoot.visitAt dynamics 10)).occurrence

def configuration {state : SpinPair.Current}
    (event : representedRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt state) :
    StageNineHolonomicConfiguration :=
  materialConfiguration (restore event).1

theorem configuration_original {state : SpinPair.Current}
    (event : representedRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt state) :
    configuration event = Recognition.wholeField state := by
  unfold configuration
  rw [Recognition.rawOccurrence_eq_emitted (restore event)]
  rfl

/-- The returned event is consumed by the original writer, installed inventory,
complete physical ledger and original macro next. The generated representation
is not installed as a replacement operational authority. -/
theorem original_consumer :
    restore event = Runtime.event.occurrence ∧
    representedRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.compile event =
      .nativeWrite (restore event) ∧
    (representedRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.compile event).nextCurrent? =
      some (SpinPair.next Runtime.visit.current) ∧
    HEq Runtime.event.wholeLedgerWriteBack (SpinPair.generatedEvolution (restore event)) ∧
    (∀ projection : SpinPair.Projection,
      HEq (SpinPair.authoritativeRoot.source.projectionLaw.project projection (restore event) PUnit.unit)
        (SpinPair.authoritativeRoot.source.projectionLaw.project projection Runtime.event.occurrence PUnit.unit)) ∧
    ClassicalWorldAcceptance Runtime.source (configuration event) ∧
    Recovery.MatterRecovery (configuration event) Recovery.stageEight ∧
    Stage9DEF.Source.restrict (configuration event) = Runtime.tick.answer ∧
    (∀ point action,
      (configuration event).conjugateMatter point (action ((configuration event).matter point)) =
        4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
          Stage9DEF.State.vectorEvaluation (Runtime.tick.answer point)
            (Stage9DEF.Compatibility.responseMatrix action)) ∧
    Runtime.tick.next.node.erase = ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ := by
  have original := Recognition.rawOccurrence_eq_generated Runtime.visit (restore event)
  refine ⟨original, rfl, rfl, Recognition.rawEvent_wholeLedger Runtime.visit (restore event),
    Recognition.rawEvent_installedFace Runtime.visit (restore event), ?_, ?_, ?_, ?_, ?_⟩
  · rw [configuration_original event]
    exact Recovery.stageOneThroughTenClosure.final.classical
  · rw [configuration_original event]
    exact Recovery.stageOneThroughTenClosure.currentMatter
  · rw [configuration_original event]
    exact Runtime.tick_answer.symm
  · rw [configuration_original event, show Recognition.wholeField Runtime.visit.current =
        Stage9C.Material.SpinPair.actual from Runtime.configuration_eq, Runtime.tick_vector]
    exact Stage9DEF.Compatibility.actual_action_quantumResponse
  · rw [← Runtime.sameOccurrenceActivation.answerNext]
    exact Runtime.sameOccurrenceActivation.macroAnswerNext

end
end SaturationMonoid.PhysicsCore.Stage10.RawSourceRealization
