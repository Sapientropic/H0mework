import H0mework.Realization.SourceComparison.History
import H0mework.Physics.MotherSource.Contact
import H0mework.Physics.MotherSource.RawSourceRealization
import H0mework.Physics.MotherDescription.Consumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RawGeneratedRoot SourceComparison
open StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineCClassicalWorldAcceptance
open Stage9C.Revision

noncomputable section

universe u
variable {foreign : Dynamics.{u}}

def reconstructed : SmoothUnifiedSource :=
  reconstruct Runtime.source.stageEight (generatedMotherCurvature Runtime.source 0 1)

theorem reconstructed_original : reconstructed = Runtime.source := reconstruct_generated Runtime.source

/-- The source is consumed at the original occurrence. The earlier source
curvature is not identified with a different action epoch's actual connection. -/
theorem source_reconstruction_consumed :
    ClassicalWorldAcceptance reconstructed Runtime.configuration ∧
    Runtime.SameOccurrenceActivation ∧
    Runtime.tick.next.node.erase = ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ := by
  refine ⟨?_, Recovery.stageOneThroughTenClosure.final.activation, ?_⟩
  · rw [reconstructed_original]
    exact Recovery.stageOneThroughTenClosure.final.classical
  · rw [← Runtime.sameOccurrenceActivation.answerNext]
    exact Runtime.sameOccurrenceActivation.macroAnswerNext

def restoredConfiguration (restore : Map foreign RawSourceRealization.dynamics) (index : ℕ) :
    StageNineHolonomicConfiguration :=
  Recognition.wholeField (SourceComparison.visit (restore.history (historyAt foreign index))).current

theorem restoredConfiguration_original (restore : Map foreign RawSourceRealization.dynamics) (index : ℕ) :
    restoredConfiguration restore index = Recognition.wholeField (SpinPair.visit index).current := by
  unfold restoredConfiguration
  rw [restore.history_at, SourceComparison.visit_at, RawGeneratedRoot.visit_current, RawSourceRealization.original_history]

/-- Local generator maps are the explicit input to this transporter. The
cross-source admission theorem must generate them, rather than assume a
completed realization, physical acceptance, inverse, or next. -/
theorem physical_recovery_consumed
    (restore : Map foreign RawSourceRealization.dynamics)
    (describe : Map RawSourceRealization.dynamics foreign) :
    (∃! comparison : Generated foreign ≃ Generated RawSourceRealization.dynamics,
      (∀ index, comparison (generatedAt foreign index) = generatedAt RawSourceRealization.dynamics index) ∧
      (∀ current, comparison (advance current) = advance (comparison current))) ∧
    (∀ index, restore.history (historyAt foreign index) = historyAt RawSourceRealization.dynamics index) ∧
    (∀ index, restore.state (currentAt foreign index) = (SpinPair.visit index).current) ∧
    ClassicalWorldAcceptance Runtime.source (restoredConfiguration restore 10) ∧
    Recovery.MatterRecovery (restoredConfiguration restore 10) Recovery.stageEight ∧
    Stage9DEF.Source.restrict (restoredConfiguration restore 10) = Runtime.tick.answer ∧
    Runtime.SameOccurrenceActivation ∧
    Runtime.tick.next.node.erase = ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ := by
  refine ⟨generated_recovery restore describe, restore.history_at,
    fun index => (restore.generated index).trans (RawSourceRealization.original_history index), ?_, ?_, ?_,
    Runtime.sameOccurrenceActivation, ?_⟩
  · rw [restoredConfiguration_original]
    exact Recovery.stageOneThroughTenClosure.final.classical
  · rw [restoredConfiguration_original]
    exact Recovery.stageOneThroughTenClosure.currentMatter
  · rw [restoredConfiguration_original]
    exact Runtime.tick_answer.symm
  · rw [← Runtime.sameOccurrenceActivation.answerNext]
    exact Runtime.sameOccurrenceActivation.macroAnswerNext

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
