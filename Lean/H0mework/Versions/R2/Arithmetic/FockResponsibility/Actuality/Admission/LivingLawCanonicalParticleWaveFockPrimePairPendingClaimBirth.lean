import H0mework.Versions.R2.Foundation.Responsibility.PendingClaimBirth
import H0mework.Versions.R2.Arithmetic.FockResponsibility.OccurrenceRuntime

/-!
# Prime-pair pending-claim birth

The sixth named Goldbach face projects the actuality debt law and its pending
state as one package-valued payload.  The exact runtime event can therefore
birth the claim without accepting a prime pair, payment, settlement, support,
target root, or next current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockPrimePairPendingClaimBirth

open PendingClaimBirth
open ParticleWaveFockOccurrenceResponsibilityRuntime
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDebt
open ParticleWaveFockOccurrenceDebtActivation

noncomputable section

/-- Closed named inventory containing only the already installed package face. -/
abbrev pendingClaimRuntimeFacade :
    SourceNativePendingClaimRuntimeFacade CanonicalUnitArithmeticRoot.N where
  base := runtimeFacade
  PendingFaceAt := fun _runtime => PUnit
  componentAt := fun _runtime _face => actualityPendingClaimProjectionLaw
  installationAt := fun _runtime _face => pendingClaimInstallation
  projectionAt := fun _runtime _face => PUnit.unit

theorem runtimePendingClaimClassifier_eq (depth : Nat) :
    actualityPendingClaimProjectionLaw.classify PUnit.unit
        (runtimeAt depth).emittedOccurrence =
      .inl (runtimeActive depth) := by
  generalize classifier_eq : actualityPendingClaimProjectionLaw.classify
    PUnit.unit (runtimeAt depth).emittedOccurrence = classification
  cases classification with
  | inl active =>
      have active_eq : active = runtimeActive depth := by
        apply PLift.down_injective
        exact Subsingleton.elim _ _
      cases active_eq
      rfl
  | inr inactive =>
      have impossible := inactive.down
      change ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
        (runtimeAt depth).current.visit.current = 0 at impossible
      rw [runtimeAt_scanIndex] at impossible
      omega

def runtimePendingClaimPackage (depth : Nat) :
    SourceGeneratedPendingClaimPackage
      (actualityPendingClaimProjectionLaw.lawAt PUnit.unit
        (runtimeAt depth).emittedOccurrence (runtimeActive depth)) :=
  actualityPendingClaimProjectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeActive depth)

theorem runtimeReadout_is_primePairPendingClaim (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) .primePairPendingClaim =
      .inl ⟨runtimeActive depth, runtimePendingClaimPackage depth⟩ := by
  change actualityPendingClaimProjectionLaw.toProjectionLaw.outcomeAt
    PUnit.unit (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifier_eq :
    actualityPendingClaimProjectionLaw.toProjectionLaw.classify PUnit.unit
      (runtimeAt depth).emittedOccurrence = classification
  cases classification with
  | inl active =>
      have active_eq : active = runtimeActive depth := by
        apply PLift.down_injective
        exact Subsingleton.elim _ _
      cases active_eq
      rfl
  | inr inactive =>
      have impossible := inactive.down
      change ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
        (runtimeAt depth).current.visit.current = 0 at impossible
      rw [runtimeAt_scanIndex] at impossible
      omega

/-- Exact active package read at one canonical runtime depth. -/
def installedPendingClaimFace (depth : Nat) :
    SourceInstalledPendingClaimFaceAt pendingClaimRuntimeFacade
      (runtimeAt depth) PUnit.unit where
  active := runtimeActive depth
  classifier_eq := runtimePendingClaimClassifier_eq depth

/-- Source-exact pending birth.  Facade, runtime and face determine its law,
state and semantic claim. -/
def pendingClaimBirth (depth : Nat) :
    SourceExactPendingClaimBirthReceiptAt pendingClaimRuntimeFacade
      (runtimeAt depth) (runtimeAt depth).tick
      (installedPendingClaimFace depth) :=
  PendingClaimBirth.generate pendingClaimRuntimeFacade
    (runtimeAt depth) (runtimeAt depth).tick
    (installedPendingClaimFace depth)

theorem pendingClaimBirth_law (depth : Nat) :
    (pendingClaimBirth depth).law =
      ParticleWaveFockPrimePairActualityDebt.activationLaw
        (runtimeActualityPayload depth) :=
  rfl

theorem pendingClaimBirth_initial (depth : Nat) :
    HEq (pendingClaimBirth depth).initial
      (StateAt.pending : StateAt (runtimeActualityPayload depth)) :=
  HEq.rfl

/-- The born row carries exactly the witness-free claim already emitted by
the actuality occurrence. -/
theorem pendingClaimBirth_claim (depth : Nat) :
    (pendingClaimBirth depth).debtEntry.claim =
      .inr (runtimeActualityPayload depth).claim :=
  rfl

theorem pendingClaimBirth_budget_positive (depth : Nat) :
    0 < (pendingClaimBirth depth).debtEntry.progressBudget :=
  (pendingClaimBirth depth).debtEntry_budget_positive

def pendingClaimBirth_target_total (depth : Nat)
    (entry : (pendingClaimBirth depth).targetLedger.Entry) :
    SourceExactPendingClaimBirthReceiptAt.TargetOriginAt
      (pendingClaimBirth depth) entry :=
  (pendingClaimBirth depth).targetOrigin entry

theorem pendingClaimBirth_has_no_old_origin (depth : Nat) :
    ¬ Nonempty (ExactTargetDebtOriginAt
      (DebtActivationLedger.inactiveLedger
        (law := (pendingClaimBirth depth).law)
        (pendingClaimBirth depth).sourceLedger.support)
      (pendingClaimBirth depth).debtEntry) := by
  rintro ⟨origin⟩
  exact nomatch origin.excludesFresh (pendingClaimBirth depth).debtFresh

theorem pendingClaimBirth_has_no_next (depth : Nat) :
    IsEmpty (pendingClaimBirth depth).GeneratedNextAt :=
  ⟨fun next => nomatch next⟩

theorem oldFactorClaim_ne_pendingActuality (depth : Nat) :
    oldFactorClaimCoordinate
        (runtimeActualityPayload depth).exactEvenOccurrence ≠
      actualityClaimCoordinate
        (runtimeActualityPayload depth).exactEvenOccurrence :=
  oldFactorClaim_ne_primePairActuality _

/-- Hostile compile-time separation: a factor-process payment cannot inhabit
the source-exact package birth type. -/
theorem oldFactorPayment_cannot_fill_pendingBirth_mouth
    (depth : Nat)
    {source target :
      ParticleWaveFockOccurrenceResponsibility.State
        (ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
          (runtimeAt depth).current.visit.current)}
    (_oldPayment : ParticleWaveFockOccurrenceResponsibility.StrictPaymentAt
      source target) : True := by
  fail_if_success
    exact (show SourceExactPendingClaimBirthReceiptAt
      pendingClaimRuntimeFacade (runtimeAt depth) (runtimeAt depth).tick
      (installedPendingClaimFace depth) from _oldPayment)
  trivial

end


end ParticleWaveFockPrimePairPendingClaimBirth
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
