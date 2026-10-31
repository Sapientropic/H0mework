import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.Critical.SourceGeneratedCriticalRelationBearer
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Exit.Root.SourceGeneratedMandateExitTargetRoot
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.SourceGeneratedLossAllocationMaterial

/-!
# Source-generated bearer lineage for the installed mandate-exit relation

The target face reuses the original election `lineageCompiler`.  Its exiting
relation is related to the existing lifecycle parent bearer by one dependent
source-law incidence; no actor equality, total bearer map or registry is
introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedMandateExitCriticalRelationBearer

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Election Relations Power Renewal Lifecycle
open M8ActualElectionMandateRenewalRegression
open M14SourceMandateRenewal
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedMandateExitTargetRoot

abbrev MandateExitRelationCompiler :=
  officeControllerRelationCompiler sourceMandateExitHistory lineageCompiler

abbrev MandateExitControllerCompiler :=
  electionActionController sourceMandateExitHistory lineageCompiler

inductive SourceMandateExitBearerLineageAt :
    MandateExitRelationCompiler.GeneratedRelation →
      Lifecycle.ActorBearer → Type
  | generated : SourceMandateExitBearerLineageAt
      (generatedOfficeControllerRelation sourceMandateExitHistory
        lineageCompiler)
      sourceGeneratedLossAllocationMaterial.parentBearer

abbrev MandateExitCriticalRelationBearerAt :=
  SourceGeneratedCriticalRelationBearerAt
    MandateExitRelationCompiler MandateExitControllerCompiler
    installedMandateExitLocalFace.standing.controller
    installedMandateExitLocalFace.standing.office
    installedMandateExitLocalFace.standing.relation
    installedMandateExitLocalFace.responsibilityConsumer.1.1
    SourceMandateExitBearerLineageAt

/-- Zero-choice producer from the installed target face. -/
def mandateExitCriticalRelationBearerAt :
    MandateExitCriticalRelationBearerAt := by
  exact SourceGeneratedCriticalRelationBearerAt.generate
    sourceGeneratedLossAllocationMaterial.parentBearer
    SourceMandateExitBearerLineageAt.generated

@[simp] theorem mandateExit_controller_relation_obligation_exact :
    installedMandateExitLocalFace.standing.controller.1 =
        installedMandateExitLocalFace.standing.relation.1.controller ∧
      installedMandateExitLocalFace.standing.relation.1.controller =
        installedMandateExitLocalFace.standing.obligation.bearer := by
  constructor <;> rfl

@[simp] theorem mandateExitCriticalRelationBearer_commonBearer_eq_parent :
    mandateExitCriticalRelationBearerAt.commonBearer =
      sourceGeneratedLossAllocationMaterial.parentBearer :=
  rfl

theorem mandateExitCriticalRelationBearer_exact_power_phase_role :
    installedMandateExitLocalFace.responsibilityConsumer.1.1 =
        mandateActionPower sourceMandateExitHistory lineageCompiler ∧
      MandateExitRelationCompiler.phaseStep
          installedMandateExitLocalFace.standing.relation = .exit ∧
      MandateExitRelationCompiler.roleAt
          installedMandateExitLocalFace.standing.relation .target = .exited := by
  rw [installedMandateExit_face_exact]
  exact ⟨rfl, rfl, sourceMandate_exit_role_is_exited⟩

theorem mandateExitCriticalRelationBearer_exact_provenance :
    (∃ seed : MandateExitRelationCompiler.ExactRelationSeed,
      (∃ state ∈ SourceMandateExitGame.occurrence.trace,
        state = (officeFace lineageCompiler).state
          SourceMandateExitGame.source ∧
        MandateExitRelationCompiler.relationSeedAt
          SourceMandateExitGame.source state seed.1 ∧
        (officeFace lineageCompiler).SeedAt SourceMandateExitGame.source state
          (MandateExitRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor MandateExitRelationCompiler =
        installedMandateExitLocalFace.standing.office ∧
      MandateExitRelationCompiler.relationOf seed =
        installedMandateExitLocalFace.standing.relation) ∧
      (∃ state ∈ SourceMandateExitGame.occurrence.trace,
        state = MandateExitControllerCompiler.actionState
          SourceMandateExitGame.source ∧
        MandateExitControllerCompiler.actionAdmittedAt
          installedMandateExitLocalFace.responsibilityConsumer.1.1.action.1) :=
  ⟨SourceGeneratedCriticalRelationBearerAt.exact_relation_provenance
      mandateExitCriticalRelationBearerAt,
    SourceGeneratedCriticalRelationBearerAt.exact_controller_provenance
      mandateExitCriticalRelationBearerAt⟩

theorem sourceMandateExitBearerLineage_commonBearer_unique
    {relation : MandateExitRelationCompiler.GeneratedRelation}
    {bearer : Lifecycle.ActorBearer}
    (lineage : SourceMandateExitBearerLineageAt relation bearer) :
    relation = generatedOfficeControllerRelation sourceMandateExitHistory
        lineageCompiler ∧
      bearer = sourceGeneratedLossAllocationMaterial.parentBearer := by
  cases lineage
  exact ⟨rfl, rfl⟩

end
end M14SourceGeneratedMandateExitCriticalRelationBearer
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitCriticalRelationBearer.mandateExitCriticalRelationBearerAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitCriticalRelationBearer.mandateExitCriticalRelationBearer_exact_power_phase_role
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitCriticalRelationBearer.mandateExitCriticalRelationBearer_exact_provenance
