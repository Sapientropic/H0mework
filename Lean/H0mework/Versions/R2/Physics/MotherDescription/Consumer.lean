import H0mework.Versions.R2.Physics.RootRuntime.RecoveryConsumer
import H0mework.Versions.R2.Physics.MotherDescription.History

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.WholeDescription

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision StageNineHolonomicField StageNineCClassicalWorldAcceptance
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open DiracExteriorMatterAction

noncomputable section

universe u

def actualDescription : Compact := weak Runtime.visit.current
def actualHistory : History := historyAt 10

theorem actual_current : decodeWeak actualDescription = Runtime.visit.current :=
  decodeWeak_weak Runtime.visit.current

theorem actual_history : decodeHistory actualHistory = Runtime.visit := decodeHistory_at 10

theorem current_history : decodeWeak actualDescription = (decodeHistory actualHistory).current := by
  rw [actual_current, actual_history]

def configuration : StageNineHolonomicConfiguration :=
  Recognition.wholeField (decodeWeak actualDescription)

theorem configuration_original : configuration = Runtime.configuration := by
  change Recognition.wholeField (decodeWeak actualDescription) = Recognition.wholeField Runtime.visit.current
  exact congrArg (fun state : Current => Recognition.wholeField state) actual_current

/-- The physical source generates both complete descriptions and the exact
original consumer. No candidate equivalence, acceptance or successor is an input. -/
theorem source_description_closed :
    (∃! comparison : Pointwise ≃ Compact,
      ∀ current, comparison (point current) = weak current) ∧
    (∀ (Index : Type u) (relation : (Index → Current) → Prop) (objects : Index → Pointwise),
      weakRelation relation (equivalence ∘ objects) ↔ pointRelation relation objects) ∧
    (∀ (Index : Type u) (operation : (Index → Current) → Current) (objects : Index → Pointwise),
      equivalence (pointOperation operation objects) = weakOperation operation (equivalence ∘ objects)) ∧
    (∃! next : Compact → Compact,
      ∀ current, next (weak current) = weak (SpinPair.next current)) ∧
    (∀ (Description : Type u) (describe : Current → Description)
      (_complete : NoIslandNoMagic.Consciousness.Representation.FaceKernelExactAt consumers describe),
      ∃! next : Set.range describe → Set.range describe,
        ∀ current, next ⟨describe current, current, rfl⟩ =
          ⟨describe (SpinPair.next current), SpinPair.next current, rfl⟩) ∧
    (∀ index, decodeHistory (historyAt index) = SpinPair.visit index) ∧
    decodeWeak actualDescription = (decodeHistory actualHistory).current ∧
    ClassicalWorldAcceptance Runtime.source configuration ∧
    Recovery.MatterRecovery configuration Recovery.stageEight ∧
    Stage9DEF.Source.restrict configuration = Runtime.tick.answer ∧
    (∀ point action,
      configuration.conjugateMatter point (action (configuration.matter point)) =
        4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
          Stage9DEF.State.vectorEvaluation (Runtime.tick.answer point)
            (Stage9DEF.Compatibility.responseMatrix action)) ∧
    HEq Runtime.event.wholeLedgerWriteBack
      (SpinPair.generatedEvolution (SpinPair.emitted (decodeWeak actualDescription))) ∧
    (∀ projection : SpinPair.Projection,
      HEq (SpinPair.authoritativeRoot.projectionOutcomeAt projection (decodeWeak actualDescription))
        (SpinPair.authoritativeRoot.projectionOutcomeAt projection Runtime.visit.current)) ∧
    weakNext actualDescription = weak (SpinPair.next (decodeHistory actualHistory).current) ∧
    Runtime.tick.next.node.erase =
      ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt (decodeHistory actualHistory)⟩ := by
  refine ⟨every_complete_description compact compact_exact,
    fun _ => every_relation, fun _ => every_operation, next_unique,
    fun _ describe complete => every_complete_action describe complete SpinPair.next, decodeHistory_at,
    current_history, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [configuration_original]
    exact Recovery.stageOneThroughTenClosure.final.classical
  · rw [configuration_original]
    exact Recovery.stageOneThroughTenClosure.currentMatter
  · rw [configuration_original]
    exact Runtime.tick_answer.symm
  · rw [configuration_original, Runtime.configuration_eq, Runtime.tick_vector]
    exact Stage9DEF.Compatibility.actual_action_quantumResponse
  · rw [actual_current]
    exact Runtime.sameOccurrenceActivation.wholeLedger
  · intro projection
    rw [actual_current]
  · rw [actual_history]
    exact weakAction_weak SpinPair.next Runtime.visit.current
  · rw [actual_history, ← Runtime.sameOccurrenceActivation.answerNext]
    exact Runtime.sameOccurrenceActivation.macroAnswerNext

end
end SaturationMonoid.PhysicsCore.Stage10.WholeDescription
