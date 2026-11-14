import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Integral.Coherent.PerfectRealization.Dependent.Effect.Residual.LivingLawRootGeneratedDependentJointPassiveResidualAuditLedgerRoot
import H0mework.Realization.Audit.LivingAuthority

/-!
# Rooted living authority of a passive dependent-face residual

An exact passive residual now specializes the generic residual living
authority without an `OpenAt` proof-irrelevance premise.  Its complete residual
type remains in the low-universe token index; the old theory epoch is read from
the original root, and the extended U7 branch is installed in the new fixed
projection inventory before emission.

The result is a direct pressure consumer of the universal root law: selected
residual row, living causal authority, rooted failure and canonical U8 coface
all arise from the same indexed occurrence.  No RH, Goldbach or Physics
coordinate equation enters this file.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open RootGeneratedResidualAdmission
open RootGeneratedResidualAuditLedger
open RootGeneratedResidualLivingAuthority
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

def passiveResidualAuditLivingRoot
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    SourceNativeLivingRootClosure (ResidualWorldAt residual) AuditV :=
  auditLivingRoot N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

abbrev passiveResidualAuditVisit
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    SourceNativeTemporalVisitAt
      (passiveResidualAuditLivingRoot residual oldU7 oldCalculus
        ).toAuthoritativeRoot.toLedgerRoot :=
  auditVisit N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

def passiveResidualAuditCausalAuthority
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (passiveResidualAuditLivingRoot residual oldU7 oldCalculus)
      (passiveResidualAuditVisit residual oldU7 oldCalculus)
      (residualWorldEntry residual) :=
  auditLivingCausalAuthority N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

def passiveResidualAuditFailureFace
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    SourceNativeRootExpressibilityFailureFaceAt
      (passiveResidualAuditLivingRoot residual oldU7 oldCalculus
        ).toAuthoritativeRoot
      (passiveResidualAuditVisit residual oldU7 oldCalculus)
      (U7 := residualExtendedU7 residual oldU7)
      (residualRepresentationFailure residual) :=
  auditFailureFace N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

def passiveResidualAuditRootedFailure
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    RootedActualExpressibilityFailureAt
      (passiveResidualAuditLivingRoot residual oldU7 oldCalculus
        ).toAuthoritativeRoot
      (passiveResidualAuditVisit residual oldU7 oldCalculus)
      (residualExtendedU7 residual oldU7)
      (residualRepresentationFailure residual) :=
  auditRootedFailure N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

def passiveResidualGeneratedMinimalCoface
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    GeneratedMinimalCofaceAt
      (passiveResidualAuditRootedFailure residual oldU7 oldCalculus) :=
  generatedMinimalCoface N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)
    root.toAuthoritativeRoot.source.lawSurface oldU7 oldCalculus

@[simp] theorem passiveResidualGeneratedDirection_boundary
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    GeneratedDirectionAt.boundary
        (rooted := passiveResidualAuditRootedFailure residual oldU7 oldCalculus)
        GeneratedDirectionAt.completion =
      residualWorldObstruction residual := by
  rfl

/-- Direct end-to-end consumer.  The first two fields retain the original
root/whole-ledger provenance; the final fields certify the new authority and
its exact residual-indexed U8 direction. -/
theorem passiveResidual_rootLawRealization_mouth
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit ∧
      Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
        (passiveResidualAuditLivingRoot residual oldU7 oldCalculus)
        (passiveResidualAuditVisit residual oldU7 oldCalculus)
        (residualWorldEntry residual)) ∧
      Nonempty (RootedActualExpressibilityFailureAt
        (passiveResidualAuditLivingRoot residual oldU7 oldCalculus
          ).toAuthoritativeRoot
        (passiveResidualAuditVisit residual oldU7 oldCalculus)
        (residualExtendedU7 residual oldU7)
        (residualRepresentationFailure residual)) ∧
      Nonempty (GeneratedMinimalCofaceAt
        (passiveResidualAuditRootedFailure residual oldU7 oldCalculus)) ∧
      GeneratedDirectionAt.boundary
          (rooted := passiveResidualAuditRootedFailure residual oldU7 oldCalculus)
          GeneratedDirectionAt.completion =
        residualWorldObstruction residual :=
  ⟨residual.wholeLedger_rooted, residual.next_rooted,
    ⟨passiveResidualAuditCausalAuthority residual oldU7 oldCalculus⟩,
    ⟨passiveResidualAuditRootedFailure residual oldU7 oldCalculus⟩,
    ⟨passiveResidualGeneratedMinimalCoface residual oldU7 oldCalculus⟩,
    rfl⟩

end

end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
