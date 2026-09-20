import H0mework.Realization.JointEffect.AuditTransition

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

open RootGeneratedCausalResidualAudit
open RootGeneratedResidualAdmission
open RootGeneratedResidualAuditLedger

universe u

namespace RootGeneratedCausalResidualAudit

variable (N : WorldRelationNetwork.{u}) (focus : N.Support)
variable (Residual : Type u) (distinguished : Residual)
variable [Subsingleton Residual]
variable (Origin : Type u) (distinguishedOrigin : Origin)

omit [Subsingleton Residual] in
/-- A sibling origin cannot enter the causal audit occurrence fibre by
reusing the same support/current label. -/
theorem siblingOrigin_isEmpty
    (current : AuditV.Current) (sibling : Origin)
    (sibling_ne : sibling ≠ distinguishedOrigin) :
    IsEmpty (Sigma fun occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current =>
      PLift (causalAuditOccurrenceOrigin N focus Residual Origin
        distinguishedOrigin occurrence = sibling)) :=
  ⟨by
    rintro ⟨occurrence, equality⟩
    exact sibling_ne (equality.down.symm.trans occurrence.2.origin_eq)⟩

end RootGeneratedCausalResidualAudit

namespace RootLawDependentJointPassiveEffect

open RootLawDependentJointStateController

noncomputable section

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {step : StepAt recognition visit}

theorem generatedPassiveCausalAudit_rejects_sibling_origin
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (sourceEvent : ExactTemporalCausalRootEventAt
      root.toAuthoritativeRoot.toLedgerRoot visit)
    (transition : SourceGeneratedPassiveResidualAuditTransitionAt residual
      oldU7 oldCalculus sourceEvent)
    (sibling : PassiveResidualCausalOriginAt residual)
    (sibling_ne : sibling ≠
      (sourceEvent.occurrence, residual.successor.targetOccurrence)) :
    IsEmpty (Sigma fun occurrence :
      transition.targetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        transition.targetVisit.current =>
      PLift (causalAuditOccurrenceOrigin N residual.support
        (ResidualCoordinateAt residual)
        (PassiveResidualCausalOriginAt residual)
        (sourceEvent.occurrence, residual.successor.targetOccurrence)
        occurrence = sibling)) :=
  siblingOrigin_isEmpty N residual.support (ResidualCoordinateAt residual)
    (PassiveResidualCausalOriginAt residual)
    (sourceEvent.occurrence, residual.successor.targetOccurrence)
    transition.targetVisit.current sibling sibling_ne

end


end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedCausalResidualAudit.siblingOrigin_isEmpty
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.generatedPassiveCausalAudit_rejects_sibling_origin
