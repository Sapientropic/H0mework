import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Installation.Consumer.ProofCarryingCycleMemoryPlatformGateActualPaidU8Update

/-!
# Relation-generated affected bearer of the admitted platform gate

The admitted gate does not receive a caller-named beneficiary.  Its exact
platform seed selects the existing cross-compiler action; that action's
relation lineage generates the lifecycle bearer and obligation.  The
different paid occurrence is connected only by the already certified
cross-occurrence transporter, and its installed platform face supplies the
independent root consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformGateAffectedBearerIncidence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal
open M3FiniteExchangeFixture
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedSequentialCrossCompilerRelationAppend
open M14SourceGeneratedActualRelationThreeCycle
open M14SourceGeneratedCycleMemoryPlatformGateObstruction
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport
open M14SourceGeneratedCycleMemoryPlatformGateU8

def platformGateAffectedBearerDepthAt (boundary : Nat) : Nat :=
  platformCycleBaseAfter boundary

theorem platformGateAffectedBearer_selectedEvent_platform
    (boundary : Nat) :
    crossCompilerSelectedEventAt
        (platformGateAffectedBearerDepthAt boundary) = .platform := by
  have seedExact := platformCycleBaseAfter_seed_platform boundary
  exact congrArg
    (fun seed : essentialAccessRelationCompiler.ExactRelationSeed =>
      (show EssentialAccessEvent from seed.1)) seedExact

def platformGateAffectedActionAt (boundary : Nat) :=
  crossCompilerSelectedActionAt (platformGateAffectedBearerDepthAt boundary)

def platformGateAffectedUpdateAt (boundary : Nat) :=
  crossCompilerSelectedUpdateAt (platformGateAffectedBearerDepthAt boundary)

def platformGateAffectedBearerAt (boundary : Nat) : Lifecycle.ActorBearer :=
  (platformGateAffectedActionAt boundary).criticalBearer.commonBearer

def platformGateSourceObligationAt (boundary : Nat) :=
  criticalRelationObligation essentialAccessCriticalBearerOf
    (crossCompilerSelectedEventAt
      (platformGateAffectedBearerDepthAt boundary))

theorem platformGateAffectedBearer_fromPlatformActor (boundary : Nat) :
    platformGateAffectedBearerAt boundary =
      exchangeLaw.bearerOfActor platformActor := by
  have bearerExact :=
    (platformGateAffectedActionAt boundary).criticalBearer.bearerLineage.bearerExact
  unfold platformGateAffectedActionAt platformGateAffectedBearerDepthAt at bearerExact
  rw [crossCompilerSelectedAction_seed_exact] at bearerExact
  change exchangeLaw.bearerOfActor
      ((actualRelationSeedAt (platformCycleBaseAfter boundary)).actor
        essentialAccessRelationCompiler) = _ at bearerExact
  rw [platformCycleBaseAfter_seed_platform] at bearerExact
  unfold platformGateAffectedBearerAt platformGateAffectedActionAt
  exact bearerExact.symm

theorem platformGateSourceObligation_bearer_exact (boundary : Nat) :
    (platformGateSourceObligationAt boundary).bearer =
      platformGateAffectedBearerAt boundary :=
  (platformGateAffectedUpdateAt boundary).bearerCommutes.symm

inductive SourceGeneratedPlatformGateAffectedBearerIncidenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 31
  | private generated

def sourceGeneratedPlatformGateAffectedBearerIncidenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedPlatformGateAffectedBearerIncidenceAt
      oldVisit sourceIndex boundary :=
  .generated

namespace SourceGeneratedPlatformGateAffectedBearerIncidenceAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  (incidence : SourceGeneratedPlatformGateAffectedBearerIncidenceAt
    oldVisit sourceIndex boundary)

theorem paidUpdate :
    ProofCarryingCycleMemoryPlatformGateActualPaidU8UpdateAt
      oldVisit sourceIndex boundary := by
  cases incidence
  exact proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
    sourceIndex boundary

def transporter :
    SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
      oldVisit sourceIndex boundary := by
  cases incidence
  exact sourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
    oldVisit sourceIndex boundary

def candidate : SourceGeneratedPlatformChannelRevisionCandidateAt boundary := by
  cases incidence
  exact sourceGeneratedPlatformChannelRevisionCandidateAt boundary

def gate : SourceGeneratedPlatformChannelGateAt
    (candidate incidence).obstruction :=
  (candidate incidence).gate

def action : type_of% (platformGateAffectedActionAt boundary) := by
  cases incidence
  exact platformGateAffectedActionAt boundary

def update : type_of% (platformGateAffectedUpdateAt boundary) := by
  cases incidence
  exact platformGateAffectedUpdateAt boundary

def affectedBearer : Lifecycle.ActorBearer := by
  cases incidence
  exact platformGateAffectedBearerAt boundary

def sourceObligation : type_of% (platformGateSourceObligationAt boundary) := by
  cases incidence
  exact platformGateSourceObligationAt boundary

theorem selectedEventPlatform :
    crossCompilerSelectedEventAt
      (platformGateAffectedBearerDepthAt boundary) = .platform := by
  cases incidence
  exact platformGateAffectedBearer_selectedEvent_platform boundary

theorem gateSeedActionExact : (gate incidence).seed =
    (action incidence).criticalBearer.bearerLineage.seed := by
  cases incidence
  change
    (sourceGeneratedPlatformChannelRevisionCandidateAt boundary).gate.seed =
      (platformGateAffectedActionAt boundary
        ).criticalBearer.bearerLineage.seed
  unfold platformGateAffectedActionAt platformGateAffectedBearerDepthAt
  rw [(sourceGeneratedPlatformChannelRevisionCandidateAt boundary
      ).gate.seed_eq_platform,
    crossCompilerSelectedAction_seed_exact]
  exact (platformCycleBaseAfter_seed_platform boundary).symm

theorem affectedBearerFromGateActor : affectedBearer incidence =
    exchangeLaw.bearerOfActor (gate incidence).actor := by
  cases incidence
  change platformGateAffectedBearerAt boundary =
    exchangeLaw.bearerOfActor
      (sourceGeneratedPlatformChannelRevisionCandidateAt boundary).gate.actor
  rw [(sourceGeneratedPlatformChannelRevisionCandidateAt boundary
    ).gate.actor_eq_platformActor]
  exact platformGateAffectedBearer_fromPlatformActor boundary

theorem obligationBearerExact : (sourceObligation incidence).bearer =
    affectedBearer incidence := by
  cases incidence
  exact platformGateSourceObligation_bearer_exact boundary

theorem targetRoleGenerated :
    (gate incidence).targetRole = EssentialAccessRole.platformProvider :=
  (gate incidence).targetRole_eq_platformProvider

def independentPaidConsumer : RenewalResponsibilityConsumerAt
    (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
      ).operationalAuthority :=
  by
    cases incidence
    exact (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
      ).rootResponsibilityConsumer

end SourceGeneratedPlatformGateAffectedBearerIncidenceAt

theorem platformGateAffectedBearerIncidence_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let incidence := sourceGeneratedPlatformGateAffectedBearerIncidenceAt
      oldVisit sourceIndex boundary
    type_of% (proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
      sourceIndex boundary) ∧
      type_of% (platformGatePaymentLineageTransport_directConsumer oldVisit
        sourceIndex boundary) ∧
      incidence.gate.seed =
        incidence.action.criticalBearer.bearerLineage.seed ∧
      incidence.affectedBearer =
        exchangeLaw.bearerOfActor incidence.gate.actor ∧
      incidence.sourceObligation.bearer = incidence.affectedBearer ∧
      incidence.gate.targetRole = EssentialAccessRole.platformProvider ∧
      Nonempty (RenewalResponsibilityConsumerAt
        (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
          ).operationalAuthority) := by
  dsimp
  let incidence := sourceGeneratedPlatformGateAffectedBearerIncidenceAt
    oldVisit sourceIndex boundary
  exact ⟨proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
      sourceIndex boundary,
    platformGatePaymentLineageTransport_directConsumer oldVisit sourceIndex
      boundary,
    incidence.gateSeedActionExact,
    incidence.affectedBearerFromGateActor,
    incidence.obligationBearerExact,
    incidence.targetRoleGenerated,
    ⟨(platformGateInstalledRenewalAt oldVisit sourceIndex boundary
      ).rootResponsibilityConsumer⟩⟩

end
end M14SourceGeneratedPlatformGateAffectedBearerIncidence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformGateAffectedBearerIncidence.platformGateAffectedBearer_selectedEvent_platform
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformGateAffectedBearerIncidence.sourceGeneratedPlatformGateAffectedBearerIncidenceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformGateAffectedBearerIncidence.platformGateAffectedBearerIncidence_directConsumer
