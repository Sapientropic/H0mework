import H0mework.Versions.R2.Realization.Audit.CausalAuthority
import H0mework.Versions.R2.Realization.JointEffect.ResidualCoface
import H0mework.Foundation.Inquiry.EmptyObstruction

/-!
# Compiler-generated passive-residual audit transition

An exact temporal source event and the controller-selected passive residual
generate one audit root.  Its concrete occurrence remembers both ends of the
original compiler step; old rows remain identity remainder and the residual
row alone generates U7 failure authority and the canonical minimal coface.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open RootGeneratedCausalResidualAudit
open RootGeneratedEmptyObstructionU7
open RootGeneratedResidualAdmission
open RootGeneratedResidualAuditLedger
open RootLawDependentJointStateController
open ObstructionGeneratedMinimalCoface

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {step : StepAt recognition visit}

abbrev PassiveResidualSourceOriginAt :=
  root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    visit.current

abbrev PassiveResidualTargetOriginAt
    (residual : RootedPassiveResidualAt step) :=
  root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    residual.successor.targetCurrent

abbrev PassiveResidualCausalOriginAt
    (residual : RootedPassiveResidualAt step) :=
  PassiveResidualSourceOriginAt (root := root) (visit := visit) ×
    PassiveResidualTargetOriginAt residual

/-- The target root is computed from the exact source event.  Its concrete
event stores both the source occurrence and the compiler-generated target
occurrence carried by the selected passive residual. -/
def passiveCausalAuditLivingRootAt
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit) :=
  causalAuditLivingRoot N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual) (PassiveResidualCausalOriginAt residual)
    (sourceEvent.occurrence, residual.successor.targetOccurrence)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

abbrev passiveCausalAuditVisitAt
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit) :=
  causalAuditVisit N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual) (PassiveResidualCausalOriginAt residual)
    (sourceEvent.occurrence, residual.successor.targetOccurrence)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

def passiveCausalAuditRootedFailureAt
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit) :=
  causalAuditRootedFailure N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual) (PassiveResidualCausalOriginAt residual)
    (sourceEvent.occurrence, residual.successor.targetOccurrence)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

def passiveCausalAuditGeneratedMinimalCofaceAt
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit) :=
  causalAuditGeneratedMinimalCoface N residual.support
    (ResidualCoordinateAt residual) (residualCoordinate residual)
    (PassiveResidualCausalOriginAt residual)
    (sourceEvent.occurrence, residual.successor.targetOccurrence)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

/-- Zero-field execution seal.  It can only be generated from the exact
source temporal occurrence; target root, audit event, row and U8 output are
dependent readouts rather than fields. -/
structure SourceGeneratedPassiveResidualAuditTransitionAt
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit) : Type (u + 5) where
  private mk ::

namespace SourceGeneratedPassiveResidualAuditTransitionAt

def generate
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceGeneratedPassiveResidualAuditTransitionAt residual oldU7
      oldCalculus sourceEvent :=
  .mk

/-- One exact source event has one generated audit transition.  A parallel
target built through the subordinate generic constructor does not inhabit
this source-indexed authority type. -/
theorem unique
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (left right : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    left = right := by
  cases left
  cases right
  rfl

def targetRoot
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (_transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :=
  passiveCausalAuditLivingRootAt residual oldU7 oldCalculus sourceEvent

abbrev targetVisit
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (_transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :=
  passiveCausalAuditVisitAt residual oldU7 oldCalculus sourceEvent

def rootedFailure
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (_transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :=
  passiveCausalAuditRootedFailureAt residual oldU7 oldCalculus sourceEvent

def minimalCoface
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (_transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :=
  passiveCausalAuditGeneratedMinimalCofaceAt residual oldU7 oldCalculus
    sourceEvent

def emittedOrigin
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    PassiveResidualCausalOriginAt residual :=
  causalAuditOccurrenceOrigin N residual.support
    (ResidualCoordinateAt residual) (PassiveResidualCausalOriginAt residual)
    (sourceEvent.occurrence, residual.successor.targetOccurrence)
    (transition.targetRoot.emitted transition.targetVisit.current)

def targetOccurrenceOrigin
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    PassiveResidualCausalOriginAt residual :=
  causalAuditOccurrenceOrigin N residual.support
    (ResidualCoordinateAt residual) (PassiveResidualCausalOriginAt residual)
    (sourceEvent.occurrence, residual.successor.targetOccurrence)
    (transition.targetRoot.emitted (ULift.up.{u, 0} true))

@[simp] theorem emittedSourceOrigin_eq
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    transition.emittedOrigin.1 = sourceEvent.occurrence :=
  rfl

@[simp] theorem emittedTargetOrigin_eq
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    transition.emittedOrigin.2 = residual.successor.targetOccurrence :=
  rfl

@[simp] theorem targetOccurrenceSourceOrigin_eq
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    transition.targetOccurrenceOrigin.1 = sourceEvent.occurrence :=
  rfl

@[simp] theorem targetOccurrenceTargetOrigin_eq
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    transition.targetOccurrenceOrigin.2 =
      residual.successor.targetOccurrence :=
  rfl

/-- Exact causal transition mouth.  The original compiler event generates a
target source whose concrete occurrence retains both ends of that compiler
step; inherited rows remain the identity remainder, while the selected
residual row alone generates audit authority and automatic U8. -/
theorem causal_transition_mouth
    {residual : RootedPassiveResidualAt step}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit}
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent) :
    residual.disposition = settlePassiveEffect step ∧
      sourceEvent.occurrence = step.sourceOccurrence ∧
      transition.emittedOrigin.1 = sourceEvent.occurrence ∧
      transition.emittedOrigin.2 = residual.successor.targetOccurrence ∧
      transition.targetOccurrenceOrigin.1 = sourceEvent.occurrence ∧
      transition.targetOccurrenceOrigin.2 =
        residual.successor.targetOccurrence ∧
      HEq sourceEvent.wholeLedgerWriteBack step.wholeLedgerWriteBack ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit ∧
      (∀ entry : OpenResponsibilityAt N residual.support,
        sourceNativeFiniteLedgerPatchGeneratedEntry?
          (causalAuditSource N residual.support (ResidualCoordinateAt residual)
            (PassiveResidualCausalOriginAt residual)
            (sourceEvent.occurrence, residual.successor.targetOccurrence))
          (causalAuditCompiler N residual.support
            (ResidualCoordinateAt residual) (residualCoordinate residual)
            (PassiveResidualCausalOriginAt residual)
            (sourceEvent.occurrence,
              residual.successor.targetOccurrence)).ExactTransitionAt
          (causalAuditCompiler N residual.support
            (ResidualCoordinateAt residual) (residualCoordinate residual)
            (PassiveResidualCausalOriginAt residual)
            (sourceEvent.occurrence,
              residual.successor.targetOccurrence)).writeRowSource
          (causalAuditCompiler N residual.support
            (ResidualCoordinateAt residual) (residualCoordinate residual)
            (PassiveResidualCausalOriginAt residual)
            (sourceEvent.occurrence,
              residual.successor.targetOccurrence)).terminalRowSource
          ((causalAuditCompiler N residual.support
            (ResidualCoordinateAt residual) (residualCoordinate residual)
            (PassiveResidualCausalOriginAt residual)
            (sourceEvent.occurrence,
              residual.successor.targetOccurrence)).compile
              (transition.targetRoot.emitted (ULift.up false)))
          ((causalAuditCompiler N residual.support
            (ResidualCoordinateAt residual) (residualCoordinate residual)
            (PassiveResidualCausalOriginAt residual)
            (sourceEvent.occurrence,
              residual.successor.targetOccurrence)).compilePatch
              (transition.targetRoot.emitted (ULift.up false)))
          (oldEntry entry) = none) ∧
      Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
        transition.targetRoot transition.targetVisit
          (residualWorldEntry residual)) ∧
      Nonempty (RootedActualExpressibilityFailureAt
        transition.targetRoot.toAuthoritativeRoot transition.targetVisit
        (residualExtendedU7 residual oldU7)
        (residualRepresentationFailure residual)) ∧
      Nonempty (GeneratedMinimalCofaceAt transition.rootedFailure) := by
  refine ⟨residual.exact, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
    residual.wholeLedger_rooted, residual.next_rooted, ?_, ?_, ?_, ?_⟩
  · intro entry
    exact causalOldEntry_is_identityRemainder N residual.support
      (ResidualCoordinateAt residual) (residualCoordinate residual)
      (PassiveResidualCausalOriginAt residual)
      (sourceEvent.occurrence, residual.successor.targetOccurrence) entry
  · exact ⟨causalAuditLivingCausalAuthority N residual.support
      (ResidualCoordinateAt residual) (residualCoordinate residual)
      (PassiveResidualCausalOriginAt residual)
      (sourceEvent.occurrence, residual.successor.targetOccurrence)
      root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus⟩
  · exact ⟨transition.rootedFailure⟩
  · exact ⟨transition.minimalCoface⟩

end SourceGeneratedPassiveResidualAuditTransitionAt

/-- Empty old obstruction vocabularies activate the transition without a
domain-supplied U7 premise. -/
def generateEmptyObstructionPassiveResidualAuditTransition
    (residual : RootedPassiveResidualAt step)
    (empty : (support : N.Support) → IsEmpty (N.ObstructionAt support))
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceGeneratedPassiveResidualAuditTransitionAt residual
      (RootGeneratedEmptyObstructionU7.producer N empty)
      (RootGeneratedEmptyObstructionU7.calculus N empty) sourceEvent :=
  SourceGeneratedPassiveResidualAuditTransitionAt.generate residual
    (RootGeneratedEmptyObstructionU7.producer N empty)
    (RootGeneratedEmptyObstructionU7.calculus N empty) sourceEvent

end


end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.SourceGeneratedPassiveResidualAuditTransitionAt.causal_transition_mouth
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.generateEmptyObstructionPassiveResidualAuditTransition
