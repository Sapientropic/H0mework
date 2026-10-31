import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Renewal.SourceInstalledRenewalProjectionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Election.ActualElectionMandateRenewalRegression

/-!
# M8 actual-election root installation

The actual-election local producer is installed as a pre-emitter coordinate
of the existing root source.  The concrete period is a regression witness;
the election producer and root-installation interfaces remain unrestricted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8ElectionRootInstallationRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Election
open M8SourceInstalledRenewalProjectionRegression
open M8ActualElectionMandateRenewalRegression

noncomputable section

abbrev electionHistory := continuingHistory 0

def electionLocalFace : ActualElectionRenewalFace electionHistory
    lineageCompiler :=
  sourceGeneratedElectionRenewal electionHistory lineageCompiler

def electionRootLaw :=
  singletonRootRenewalLaw
    (electionGame electionHistory)
    (electionActionController electionHistory lineageCompiler).actionSeedAt
    (ElectionRenewalConsumerAt electionHistory lineageCompiler)
    (ElectionRenewalDispositionAt electionHistory lineageCompiler)
    electionLocalFace.sourceSeed electionLocalFace.responsibilityConsumer
    electionLocalFace.exactDisposition

abbrev electionInstalledRoot := rootWithRenewalLaw electionRootLaw
abbrev electionRootVisit := initialVisitWithRenewalLaw electionRootLaw
abbrev electionRootRecognition := recognitionWithRenewalLaw electionRootLaw

def electionInstalledRenewal :
    SourceInstalledRenewalAt electionRootRecognition electionRootVisit :=
  installedAtInitialVisit electionRootLaw PUnit.unit rfl

def electionRootLocalFace :=
  electionInstalledRenewal.localFace
    (fun _ exactSeed => lineageCompiler.controllerOf
      exactSeed.1.controllerSeed)
    (mandateStandingOf electionHistory lineageCompiler)

@[simp] theorem election_root_seed_exact :
    electionRootLocalFace.sourceSeed = electionLocalFace.sourceSeed :=
  rfl

@[simp] theorem election_root_power_consumer_exact :
    electionRootLocalFace.responsibilityConsumer.1.1 =
      mandateActionPower electionHistory lineageCompiler :=
  rfl

theorem election_root_M1_consumer_exact :
    Nonempty (SourceOwnsResponsibilityIncidence
      (mandateVocabulary lineageCompiler) electionHistory.current
      (mandateObligation lineageCompiler electionHistory.current)) :=
  ⟨electionRootLocalFace.responsibilityConsumer.2⟩

theorem election_root_mandate_continues_live :
    electionRootLocalFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler electionHistory.current).val]? =
      some (.live (mandateObligation lineageCompiler
        electionHistory.current)) :=
  electionRenewal_continues_live electionHistory lineageCompiler rfl

structure ElectionRootInstallationCertificate : Type 3 where
  installed : SourceInstalledRenewalAt electionRootRecognition electionRootVisit
  exactLocalFace : ActualElectionRenewalFace electionHistory lineageCompiler
  sourceSeedExact : exactLocalFace.sourceSeed = electionLocalFace.sourceSeed
  exactPower : exactLocalFace.responsibilityConsumer.1.1 =
    mandateActionPower electionHistory lineageCompiler
  rootConsumer : RenewalResponsibilityConsumerAt installed.operationalAuthority
  rootProjectionAndNext :
    let evolution := electionInstalledRoot.canonicalCausalAnswerAndNext
      (ULift.up electionRootVisit)
    evolution.generated =
        electionInstalledRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          electionRootVisit ∧
      HEq (evolution.generated.projectionOutcome
          electionRootRecognition.rootProjection)
        (electionRootRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (electionInstalledRoot.emitted electionRootVisit.current)) ∧
      evolution.nextCurrent =
        electionInstalledRoot.generatedNextCurrentAt electionRootVisit

def electionRootInstallationDirectConsumer :
    ElectionRootInstallationCertificate where
  installed := electionInstalledRenewal
  exactLocalFace := electionRootLocalFace
  sourceSeedExact := election_root_seed_exact
  exactPower := election_root_power_consumer_exact
  rootConsumer := electionInstalledRenewal.rootResponsibilityConsumer
  rootProjectionAndNext :=
    electionInstalledRenewal.rootAnswerAndNext_factorizes

end
end M8ElectionRootInstallationRegression
end Society
end ProcessGame
end SaturationMonoid
