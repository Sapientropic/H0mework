import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Compiler.SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot

/-!
# Pair-intent proof-carrying renewal source

The active pair-intent occurrence receives one pre-emitter proof-carrying
renewal law.  Its local seed, lifecycle, residual bearer, observer vertical
and disposition are the existing M9 producers.  The target root contributes
only its own active occurrence, existing bearer row, identity whole-ledger
patch and ordinary successor.  No renewal is available at ingress `false`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Legislation
open M9ProofCarryingRenewalInquiryRoot
open M8RelationshipMaintenanceRenewalRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler

/-- Exact proof-carrying payload at the M9 visit which generated this
pair-intent line.  The target renewal law reads this installed producer rather
than reconstructing its seed, residual or observer kernel. -/
def representationIntentOriginInstalledProofCarryingRenewalAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceInstalledRenewalAt jointRecognition
      (.finite
        (M14SourceGeneratedPostSettlementObserverSubmissionU8.oldRootVisitAt
          oldVisit sourceIndex boundary)) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def representationIntentProofCarryingRenewalShellAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRenewalRootShellAt
      (representationIntentRestructuringSource oldVisit sourceIndex boundary
        ).toLedgerSource where
  ActiveAt := fun {current} _occurrence => PLift (current = true)
  InactiveAt := fun {current} _occurrence => PLift (current ≠ true)
  classify := by
    intro current occurrence
    by_cases current_eq : current = true
    · exact .inl ⟨current_eq⟩
    · exact .inr ⟨current_eq⟩
  sourceEntry := by
    intro current occurrence active
    cases active.down
    have occurrence_eq := representationIntentOccurrence_eq_emitted oldVisit
      sourceIndex boundary occurrence
    cases occurrence_eq
    exact representationResidualBearerAt oldVisit sourceIndex boundary
  selectedRow := by
    intro current occurrence active
    cases active.down
    have occurrence_eq := representationIntentOccurrence_eq_emitted oldVisit
      sourceIndex boundary occurrence
    cases occurrence_eq
    let source :=
      (representationIntentRestructuringSource oldVisit sourceIndex boundary
        ).toLedgerSource
    exact
      (sourceNativeFiniteLedgerPatchGeneratedEntry?
        source.source source.ledgerCompiler.ExactTransitionAt
        source.ledgerCompiler.writeRowSource
        source.ledgerCompiler.terminalRowSource
        (source.ledgerCompiler.compile
          (representationIntentEmitted oldVisit sourceIndex boundary true))
        (source.ledgerCompiler.compilePatch
          (representationIntentEmitted oldVisit sourceIndex boundary true))
        (representationResidualBearerAt oldVisit sourceIndex boundary)).get
          (by rfl)
  successor := by
    intro current occurrence active
    cases active.down
    have occurrence_eq := representationIntentOccurrence_eq_emitted oldVisit
      sourceIndex boundary occurrence
    cases occurrence_eq
    exact
      (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
        ((representationIntentLedgerCompiler oldVisit sourceIndex boundary
          ).compile
            (representationIntentEmitted oldVisit sourceIndex boundary
              true))).get (by rfl)
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence leftActive
      rightActive
    cases leftActive.down
    cases rightActive.down
    have left_eq := representationIntentOccurrence_eq_emitted oldVisit
      sourceIndex boundary leftOccurrence
    have right_eq := representationIntentOccurrence_eq_emitted oldVisit
      sourceIndex boundary rightOccurrence
    cases left_eq
    cases right_eq
    rfl

def representationIntentProofCarryingRenewalLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRenewalProjectionLaw
      (representationIntentRestructuringSource oldVisit sourceIndex boundary
        ).toLedgerSource
      LocalGame LocalSeed LocalSeedAt RenewalConsumerAt LocalDispositionAt :=
  SourceNativeRenewalProjectionLaw.ofRootShell
    (representationIntentProofCarryingRenewalShellAt oldVisit sourceIndex
      boundary)
    (representationIntentOriginInstalledProofCarryingRenewalAt oldVisit
      sourceIndex boundary).payload.sourceSeed
    (representationIntentOriginInstalledProofCarryingRenewalAt oldVisit
      sourceIndex boundary).payload.consumer
    (representationIntentOriginInstalledProofCarryingRenewalAt oldVisit
      sourceIndex boundary).payload.disposition

def representationIntentProofCarryingRenewalActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProofCarryingRenewalLawAt oldVisit sourceIndex
      boundary).ActiveAt
        (representationIntentEmitted oldVisit sourceIndex boundary true) :=
  ⟨rfl⟩

@[simp] theorem representationIntentProofCarryingRenewalClassifier_true
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProofCarryingRenewalLawAt oldVisit sourceIndex
      boundary).classify
        (representationIntentEmitted oldVisit sourceIndex boundary true) =
      .inl
        (representationIntentProofCarryingRenewalActiveAt oldVisit sourceIndex
          boundary) := by
  dsimp [representationIntentProofCarryingRenewalLawAt,
    SourceNativeRenewalProjectionLaw.ofRootShell,
    representationIntentProofCarryingRenewalShellAt,
    representationIntentProofCarryingRenewalActiveAt]
  split
  · apply congrArg Sum.inl
    exact Subsingleton.elim _ _
  · contradiction

theorem representationIntentProofCarryingRenewal_ingress_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty
      ((representationIntentProofCarryingRenewalLawAt oldVisit sourceIndex
        boundary).ActiveAt
          (representationIntentEmitted oldVisit sourceIndex boundary false)) :=
  ⟨fun active => Bool.noConfusion active.down⟩

theorem representationIntentProofCarryingRenewal_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let law := representationIntentProofCarryingRenewalLawAt oldVisit
      sourceIndex boundary
    let active := representationIntentProofCarryingRenewalActiveAt oldVisit
      sourceIndex boundary
    let payload := law.compile
      (representationIntentEmitted oldVisit sourceIndex boundary true) active
    payload.sourceEntry =
        representationResidualBearerAt oldVisit sourceIndex boundary ∧
      payload.sourceSeed =
        (representationIntentOriginInstalledProofCarryingRenewalAt oldVisit
          sourceIndex boundary).payload.sourceSeed ∧
      payload.consumer =
        (representationIntentOriginInstalledProofCarryingRenewalAt oldVisit
          sourceIndex boundary).payload.consumer ∧
      payload.disposition =
        (representationIntentOriginInstalledProofCarryingRenewalAt oldVisit
          sourceIndex boundary).payload.disposition ∧
      payload.successor.targetCurrent = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal.representationIntentProofCarryingRenewalLawAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal.representationIntentOriginInstalledProofCarryingRenewalAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal.representationIntentProofCarryingRenewalClassifier_true
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal.representationIntentProofCarryingRenewal_ingress_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal.representationIntentProofCarryingRenewal_directConsumer
