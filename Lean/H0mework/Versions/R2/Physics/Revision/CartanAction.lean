import H0mework.Versions.R2.Physics.Revision.MaterialSource

/-! One fixed first-assembly occurrence generates the Cartan material action.
The exact old row enters unchanged; the target source's first whole-ledger
write generates the qualified Cartan actual and its subsequent P286 action.
This is a sequential actual action, with no expressibility-failure premise. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField

noncomputable section

def firstAssemblyActionSourceEvent :
    ExactTemporalCausalRootEventAt sourceNativeRoot afterGravityTemporalVisit :=
  sourceNativeRoot.generatedAtTemporalVisit afterGravityTemporalVisit

private def firstAssemblyOccurrencePresentation :
    ConstructivePresentation
      (livingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        afterGravityTemporalVisit.current)
      (materialLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        materialLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => materialEmitted .ingress
  backward := fun _ => firstAssemblyActionSourceEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change RootNativeEventAt firstAssemblyCurrent support at event
    cases event.support_eq
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change MaterialEventAt .ingress support at event
    cases event.support_eq
    rfl

/-- Four whole-field consequences of the first generated material write.
The configuration is read through the target root's installed projection. -/
structure CartanFirstWriteReceiptAt
    (sourceEvent : ExactTemporalCausalRootEventAt
      sourceNativeRoot afterGravityTemporalVisit)
    (answer : StageNineHolonomicConfiguration) : Type 3 where
  sourceExact : sourceEvent = firstAssemblyActionSourceEvent
  configurationProjection :
    materialAuthoritativeRoot.projectionOutcomeAt .configuration
        materialFirstSuccessor.targetCurrent = .inl ⟨PUnit.unit, answer⟩
  residualProjection :
    materialAuthoritativeRoot.projectionOutcomeAt .residual
        materialFirstSuccessor.targetCurrent =
      .inl ⟨PUnit.unit, materialResidual
        (materialCurrentSupport materialFirstSuccessor.targetCurrent)⟩
  gravityMultiplier : ∀ point,
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      answer point).gravityMultiplier = 0
  gravityAuxiliary : ∀ point,
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      answer point).gravityAuxiliary = 0
  p286Auxiliary : ∀ point,
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      answer point).p286GaugeAuxiliary = 0
  lorentzConnection : ∀ point,
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      answer point).lorentzConnection = 0

private def firstAssemblyActionTargetAt
    (sourceEvent : ExactTemporalCausalRootEventAt
      sourceNativeRoot afterGravityTemporalVisit) :
    SourceNativeSequentialActualActionTargetAt livingRoot
      afterGravityTemporalVisit sourceEvent
      (rootLedgerEntry firstAssemblyCurrent) afterGravityCausalEntryAuthority := by
  rw [sourceEvent.eq_generated]
  exact
    { TargetN := MaterialN
      translation := materialTranslation
      TargetV := MaterialV
      targetRoot := materialLivingRoot
      targetTheory := TheoryState.rootSemantic MaterialN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := id
          commuting := fun _ => rfl }
      occurrencePresentation := firstAssemblyOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := materialTranslation.oldOpenLedger firstAssemblyCurrent
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := materialIngress_has_no_fresh_rows firstAssemblyCurrent
      translatedSourceEntryRow := materialInitialEntryRow
      firstSuccessor := materialFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := StageNineHolonomicConfiguration
      answer := materialConfiguration
        (materialCurrentSupport materialFirstSuccessor.targetCurrent)
      Receipt := fun answer => CartanFirstWriteReceiptAt
        firstAssemblyActionSourceEvent answer
      receipt :=
        { sourceExact := rfl
          configurationProjection := rfl
          residualProjection := rfl
          gravityMultiplier := Material.firstAssemblyCartanActual_gravityMultiplier_zero
          gravityAuxiliary := Material.firstAssemblyCartanActual_gravityAuxiliary_zero
          p286Auxiliary := Material.firstAssemblyCartanActual_p286Auxiliary_zero
          lorentzConnection := Material.firstAssemblyCartanActual_lorentz_zero } }

/-- The sole input of this fixed action compiler is the registered source
event; target material, ledger, first write and next are internal readouts. -/
def firstAssemblyActionProgram :
    SourceNativeSequentialActualActionProgramAt livingRoot
      afterGravityTemporalVisit (rootLedgerEntry firstAssemblyCurrent)
      afterGravityCausalEntryAuthority where
  targetAt := firstAssemblyActionTargetAt

def firstAssemblyGeneratedCartanAction :
    SourceGeneratedSequentialActualActionAt firstAssemblyActionProgram
      firstAssemblyActionSourceEvent :=
  firstAssemblyActionProgram.generate firstAssemblyActionSourceEvent

/-- The action consumer reads exactly the newly generated whole-field actual. -/
theorem firstAssemblyGeneratedCartanAction_answer :
    firstAssemblyGeneratedCartanAction.answer = Material.firstAssemblyCartanActual :=
  rfl

def firstAssemblyGeneratedCartanAction_receipt :
    CartanFirstWriteReceiptAt firstAssemblyActionSourceEvent
      Material.firstAssemblyCartanActual :=
  firstAssemblyGeneratedCartanAction.receipt

theorem firstAssemblyGeneratedCartanAction_next :
    firstAssemblyGeneratedCartanAction.target.targetAnswerAndNext.nextCurrent =
      ⟨MaterialV, materialAuthoritativeRoot,
        firstAssemblyGeneratedCartanAction.target.targetVisit⟩ :=
  firstAssemblyGeneratedCartanAction.target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision
