import H0mework.Versions.R2.Realization.JointEffect.Residual
import H0mework.Versions.R2.Realization.Audit.U7Coface

/-!
# Free obstruction coface of an exact passive residual

The full passive residual remains indexed by its exact root step.  Its
low-universe canonical token is fed to the generic residual-world coface,
which generates a faithful obstruction, causal row, operational theory
failure and U7 theory-audit branch.  No old obstruction inhabitant, domain
equation, target row or U8 result is a premise.

This file does not yet lift the old root compiler to the enlarged whole
ledger.  That causal finite-patch installation is the next controller seam.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open RootGeneratedResidualAdmission
open RootLawDependentJointStateController

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

abbrev ResidualCoordinateAt (residual : RootedPassiveResidualAt step) :=
  RootedPassiveResidualTokenAt residual

def residualCoordinate (residual : RootedPassiveResidualAt step) :
    ResidualCoordinateAt residual :=
  RootedPassiveResidualTokenAt.generate residual

abbrev ResidualWorldAt (residual : RootedPassiveResidualAt step) :=
  ExtendedNetwork N residual.support (ResidualCoordinateAt residual)

def residualWorldEntry (residual : RootedPassiveResidualAt step) :
    OpenResponsibilityAt (ResidualWorldAt residual) residual.support :=
  residualEntry residual.support (residualCoordinate residual)

def residualWorldObstruction (residual : RootedPassiveResidualAt step) :
    (ResidualWorldAt residual).ObstructionAt residual.support :=
  residualObstruction residual.support (residualCoordinate residual)

def residualWorldExtensionReceipt
    (residual : RootedPassiveResidualAt step) :
    (ResidualWorldAt residual).DispositionAt
      residual.support .lawSurfaceExtension :=
  residualExtensionReceipt residual.support (residualCoordinate residual)

/-- Operational theory generated from the exact old law surface.  It remains
faithful on old claims and intentionally has no expression constructor for
the newly adjoined residual coordinate. -/
def residualOperationalTheory (residual : RootedPassiveResidualAt step) :
    TheoryState (ResidualWorldAt residual) :=
  liftTheory residual.support root.toAuthoritativeRoot.source.lawSurface

def residualRepresentationFailure
    (residual : RootedPassiveResidualAt step) :
    ActualExpressibilityFailure (residualOperationalTheory residual)
      (residualWorldObstruction residual) :=
  residualFailure residual.support
    root.toAuthoritativeRoot.source.lawSurface (residualCoordinate residual)

theorem residualWorldObstruction_faithful
    (residual : RootedPassiveResidualAt step) :
    Function.Injective
      (residualObstruction (N := N) residual.support
        (Residual := ResidualCoordinateAt residual)) :=
  residualObstruction_injective residual.support _

theorem residualWorld_row_claim_eq_obstruction
    (residual : RootedPassiveResidualAt step) :
    (residualWorldEntry residual).claim =
      (ResidualWorldAt residual).obstructionClaim
        (residualWorldObstruction residual) :=
  rfl

/-- Exact coface mouth before causal root installation. -/
theorem residualWorldCofaceMouth
    (residual : RootedPassiveResidualAt step) :
    HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit ∧
      (residualWorldEntry residual).claim =
        (ResidualWorldAt residual).obstructionClaim
          (residualWorldObstruction residual) ∧
      Nonempty (ActualExpressibilityFailure
        (residualOperationalTheory residual)
        (residualWorldObstruction residual)) :=
  ⟨residual.wholeLedger_rooted, residual.next_rooted,
    residualWorld_row_claim_eq_obstruction residual,
    ⟨residualRepresentationFailure residual⟩⟩

def residualExtendedU7
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N) :
    U7ProducerCalculus (ResidualWorldAt residual) :=
  extendU7 residual.support oldU7

def residualExtendedU7Calculus
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    U7ObstructionEvolutionCalculus (ResidualWorldAt residual)
      (residualExtendedU7 residual oldU7) :=
  extendU7Calculus residual.support oldU7 oldCalculus

theorem residualExtendedU7_demandEntry_eq
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    U7ActualSuccessorSource.demandEntry
        ((residualExtendedU7Calculus residual oldU7 oldCalculus).source.emit
          (residualWorldObstruction residual)) =
      residualWorldEntry residual :=
  residual_u7_demand_entry residual.support oldU7 oldCalculus
    (residualCoordinate residual)

def residualExtendedU7_theoryAudit
    (residual : RootedPassiveResidualAt step)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    SourceNativeU7TheoryAuditAt
      (residualExtendedU7Calculus residual oldU7 oldCalculus)
      ((residualExtendedU7Calculus residual oldU7 oldCalculus).source.emit
        (residualWorldObstruction residual)) :=
  residual_u7_theoryAudit residual.support oldU7 oldCalculus
    (residualCoordinate residual)

end

end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
