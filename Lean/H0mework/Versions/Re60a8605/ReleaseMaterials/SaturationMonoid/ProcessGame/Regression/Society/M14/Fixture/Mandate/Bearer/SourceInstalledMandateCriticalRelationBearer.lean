import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.Critical.SourceGeneratedCriticalRelationBearer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.PeriodicMandatePowerRenewal
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.SourceGeneratedLossAllocationMaterial

/-!
# Source-installed mandate critical-relation bearer

The periodic M9/M14 mandate face is already installed at every exact temporal
visit.  This file does not replace its election lineage compiler.  It adds one
source-owned dependent incidence from the face's original office relation and
controller/obligation lineage to the existing lifecycle residual bearer.

The public producer accepts only a depth.  Relation, controller, power,
phase, role, whole-ledger row and generated next are projections of
`periodicMandatePowerRenewalAt depth`; no actor equality, bearer equation,
compiler, root shell or target verdict is accepted from a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceInstalledMandateCriticalRelationBearer

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Election Relations Power Renewal Lifecycle
open M8ActualElectionMandateRenewalRegression
open M14SourceMandateRenewal
open M14PeriodicMandatePowerRenewal
open M14SourceGeneratedLossAllocationMaterial

abbrev MandateRelationCompiler :=
  officeControllerRelationCompiler sourceMandateHistory lineageCompiler

abbrev MandateControllerCompiler :=
  electionActionController sourceMandateHistory lineageCompiler

/-- Single source-law incidence.  It is indexed by one exact generated
relation and one existing lifecycle bearer; it is not a total Nat-to-bearer
map or registry. -/
inductive SourceMandateBearerLineageAt :
    MandateRelationCompiler.GeneratedRelation →
      Lifecycle.ActorBearer → Type
  | generated : SourceMandateBearerLineageAt
      (generatedOfficeControllerRelation sourceMandateHistory lineageCompiler)
      sourceGeneratedLossAllocationMaterial.parentBearer

/-- The installed face computes controller, relation lineage controller and
obligation bearer from the same original controller seed. -/
@[simp] theorem installedMandate_controller_relation_obligation_exact
    (depth : Nat) :
    (periodicMandatePowerRenewalAt depth).localFace.standing.controller.1 =
        (periodicMandatePowerRenewalAt depth
          ).localFace.standing.relation.1.controller ∧
      (periodicMandatePowerRenewalAt depth
        ).localFace.standing.relation.1.controller =
        (periodicMandatePowerRenewalAt depth
          ).localFace.standing.obligation.bearer := by
  constructor <;> rfl

abbrev InstalledMandateCriticalRelationBearerAt (depth : Nat) :=
  SourceGeneratedCriticalRelationBearerAt
    MandateRelationCompiler MandateControllerCompiler
    (periodicMandatePowerRenewalAt depth).localFace.standing.controller
    (periodicMandatePowerRenewalAt depth).localFace.standing.office
    (periodicMandatePowerRenewalAt depth).localFace.standing.relation
    (periodicMandatePowerRenewalAt depth
      ).localFace.responsibilityConsumer.1.1
    SourceMandateBearerLineageAt

/-- Zero-choice generation from the already installed face. -/
def installedMandateCriticalRelationBearerAt (depth : Nat) :
    InstalledMandateCriticalRelationBearerAt depth := by
  exact SourceGeneratedCriticalRelationBearerAt.generate
    sourceGeneratedLossAllocationMaterial.parentBearer
    SourceMandateBearerLineageAt.generated

/-- Root-installed seal for the new dependent incidence.  The root data are
not copied into a new root; they remain fields of the exact periodic mandate
seal retained here. -/
structure SourceInstalledMandateCriticalRelationBearerAt
    (depth : Nat) : Type 32 where
  private mk ::
  mandate : SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt depth
  mandateExact : mandate = periodicMandatePowerRenewalAt depth
  criticalBearer : InstalledMandateCriticalRelationBearerAt depth
  criticalBearerExact : criticalBearer =
    installedMandateCriticalRelationBearerAt depth

/-- Sole authoritative producer. -/
def sourceInstalledMandateCriticalRelationBearerAt (depth : Nat) :
    SourceInstalledMandateCriticalRelationBearerAt depth :=
  { mandate := periodicMandatePowerRenewalAt depth
    mandateExact := rfl
    criticalBearer := installedMandateCriticalRelationBearerAt depth
    criticalBearerExact := rfl }

namespace SourceInstalledMandateCriticalRelationBearerAt

variable {depth : Nat}
variable (installed : SourceInstalledMandateCriticalRelationBearerAt depth)

/-- Installed power, relation phase and target role remain the original
continuing mandate values; this carrier does not falsely report a loss. -/
theorem exact_power_phase_role :
    installed.mandate.localFace.responsibilityConsumer.1.1 =
        mandateActionPower sourceMandateHistory lineageCompiler ∧
      MandateRelationCompiler.phaseStep
          installed.mandate.localFace.standing.relation = .renew ∧
      MandateRelationCompiler.roleAt
          installed.mandate.localFace.standing.relation .target = .held := by
  rw [installed.mandateExact,
    (periodicMandatePowerRenewalAt depth).localFaceExact]
  exact ⟨rfl, rfl, rfl⟩

/-- The root occurrence, shared row/successor, whole-ledger write and
generated next are exactly those of the installed periodic seal. -/
theorem root_authority_commutes :
    installed.mandate.rootOccurrence =
        (M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot
          |>.toLedgerRoot |>.exactTemporalCausalEventAt
            (M14UBIPeriodicRootHistory.temporalVisitAt depth)) ∧
      installed.mandate.installed.RootAnswerAndNextFactorizes ∧
      installed.mandate.generatedNext =
        M9ProofCarryingRenewalInquiryRoot.jointRoot.generatedNextCurrentAt
          (M14UBIPeriodicRootHistory.temporalVisitAt depth) :=
  ⟨installed.mandate.rootOccurrenceExact,
    installed.mandate.rootFactorization,
    installed.mandate.generatedNextExact⟩

@[simp] theorem commonBearer_eq_parent :
    installed.criticalBearer.commonBearer =
      sourceGeneratedLossAllocationMaterial.parentBearer := by
  rw [installed.criticalBearerExact]
  rfl

include installed
/-- Source relation and controller provenance are inherited from the exact
installed power indexed by the generic carrier. -/
theorem exact_relation_and_controller_provenance :
    (∃ seed : MandateRelationCompiler.ExactRelationSeed,
      (∃ state ∈ SourceMandateGame.occurrence.trace,
        state = (officeFace lineageCompiler).state SourceMandateGame.source ∧
        MandateRelationCompiler.relationSeedAt SourceMandateGame.source state
          seed.1 ∧
        (officeFace lineageCompiler).SeedAt SourceMandateGame.source state
          (MandateRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor MandateRelationCompiler =
        (periodicMandatePowerRenewalAt depth).localFace.standing.office ∧
      MandateRelationCompiler.relationOf seed =
        (periodicMandatePowerRenewalAt depth
          ).localFace.standing.relation) ∧
      (∃ state ∈ SourceMandateGame.occurrence.trace,
        state = MandateControllerCompiler.actionState SourceMandateGame.source ∧
          MandateControllerCompiler.actionAdmittedAt
            (periodicMandatePowerRenewalAt depth
              ).localFace.responsibilityConsumer.1.1.action.1) :=
  ⟨SourceGeneratedCriticalRelationBearerAt.exact_relation_provenance
      installed.criticalBearer,
    SourceGeneratedCriticalRelationBearerAt.exact_controller_provenance
      installed.criticalBearer⟩

end SourceInstalledMandateCriticalRelationBearerAt

/-- The source law admits only the existing parent bearer. -/
theorem sourceMandateBearerLineage_commonBearer_unique
    {relation : MandateRelationCompiler.GeneratedRelation}
    {bearer : Lifecycle.ActorBearer}
    (lineage : SourceMandateBearerLineageAt relation bearer) :
    relation = generatedOfficeControllerRelation sourceMandateHistory
        lineageCompiler ∧
      bearer = sourceGeneratedLossAllocationMaterial.parentBearer := by
  cases lineage
  exact ⟨rfl, rfl⟩

end
end M14SourceInstalledMandateCriticalRelationBearer
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateCriticalRelationBearer.installedMandateCriticalRelationBearerAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateCriticalRelationBearer.sourceInstalledMandateCriticalRelationBearerAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateCriticalRelationBearer.SourceInstalledMandateCriticalRelationBearerAt.exact_power_phase_role
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateCriticalRelationBearer.SourceInstalledMandateCriticalRelationBearerAt.root_authority_commutes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateCriticalRelationBearer.SourceInstalledMandateCriticalRelationBearerAt.commonBearer_eq_parent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateCriticalRelationBearer.sourceMandateBearerLineage_commonBearer_unique
