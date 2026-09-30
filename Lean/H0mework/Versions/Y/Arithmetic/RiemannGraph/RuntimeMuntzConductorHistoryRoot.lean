import H0mework.Versions.Y.Arithmetic.RiemannGraph.RuntimeMuntzConductorHistoryMaterial

/-!
# Fixed-root conductor-history activation

The function-valued conductor successor history is installed as a projection
coface of the existing all-place Weil root.  The lower source, emitter,
whole ledger and generated next are inherited; the history cannot choose a
successor or replace the already installed Euler--Müntz face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History

open CanonicalUnitArithmeticRoot
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open CofinalFaithfulSettlementFace
open Material
open Root

noncomputable section

def runtimeConductorHistoryAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeAllPlaceWeilAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimeConductorFaithfulMaterialLaw
        observation nontrivial).toProjectionLaw

def runtimeConductorHistoryLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimeConductorHistoryAuthoritySource observation nontrivial
  terminalHandoff :=
    (runtimeConductorHistoryAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimeConductorHistoryRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimeConductorHistoryLivingSource observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimeConductorHistoryRoot_reuses_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeConductorHistoryRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimeConductorHistoryRoot observation nontrivial).emitted = emitted :=
  ⟨rfl, rfl⟩

def runtimeConductorHistoryInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeConductorFaithfulMaterialLaw
        observation nontrivial).toProjectionLaw
      (runtimeConductorHistoryAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimeAllPlaceWeilAuthoritySource observation nontrivial)
    (runtimeConductorFaithfulMaterialLaw
      observation nontrivial).toProjectionLaw

def runtimeConductorHistoryInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeAllPlaceWeilAuthoritySource
        observation nontrivial).projectionLaw
      (runtimeConductorHistoryAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimeAllPlaceWeilAuthoritySource observation nontrivial)
    (runtimeConductorFaithfulMaterialLaw
      observation nontrivial).toProjectionLaw

def runtimeAllPlaceWeilInstallationAtConductorHistoryRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeAllPlaceWeilProjectionLaw observation nontrivial)
      (runtimeConductorHistoryAuthoritySource
        observation nontrivial).projectionLaw :=
  (runtimeAllPlaceWeilInstallation observation nontrivial).trans
    (runtimeConductorHistoryInheritedInstallation
      observation nontrivial)

/-- The pre-existing joint relation remains installed at the conductor
history root through the inherited all-place coface. -/
def runtimeJointFaithfulInstallationAtConductorHistoryRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeConductorHistoryAuthoritySource
        observation nontrivial).projectionLaw :=
  (runtimeJointFaithfulInstallationAtAllPlaceWeilRoot
    observation nontrivial).trans
      (runtimeConductorHistoryInheritedInstallation
        observation nontrivial)

/-- The existing effect law is inherited by the same route; conductor
history does not create a replacement effect vocabulary. -/
def runtimeEffectInstallationAtConductorHistoryRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectLaw observation nontrivial).toProjectionLaw
      (runtimeConductorHistoryAuthoritySource
        observation nontrivial).projectionLaw :=
  (runtimeEffectInstallationAtAllPlaceWeilRoot observation nontrivial).trans
    (runtimeConductorHistoryInheritedInstallation
      observation nontrivial)

def runtimeConductorHistoryRecognition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalFaithfulRecognitionAt ConductorHistoryCarrier
      (runtimeConductorHistoryRoot observation nontrivial) :=
  SourceNativeCofinalFaithfulRecognitionAt.create
    (runtimeConductorFaithfulMaterialLaw observation nontrivial)
    (runtimeConductorHistoryInstallation observation nontrivial)

def runtimeConductorHistoryVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimeConductorHistoryRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

def runtimeConductorHistoryStepAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    RootGeneratedCofinalFaithfulSettlementStepAt
      (runtimeConductorHistoryRecognition observation nontrivial)
      (runtimeConductorHistoryVisitAt observation nontrivial depth) :=
  (runtimeConductorHistoryRecognition observation nontrivial).generateStepAt
    (runtimeConductorHistoryVisitAt observation nontrivial depth)

@[simp] theorem runtimeConductorHistoryStepAt_seed_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeConductorHistoryStepAt observation nontrivial depth
      ).history.seed.root =
        conductorSuccessorPresentedEvent 0 := by
  rfl

/-- The installed history is the same source projection and inherits the
canonical whole-ledger write and next current. -/
theorem runtimeConductorHistoryStep_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeConductorHistoryStepAt
      observation nontrivial depth
    HEq step.wholeLedgerWriteBack
        ((runtimeConductorHistoryRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimeConductorHistoryVisitAt
              observation nontrivial depth).current) ∧
      step.nextCurrent =
        (runtimeConductorHistoryRoot observation nontrivial
          ).generatedNextCurrentAt
            (runtimeConductorHistoryVisitAt
              observation nontrivial depth) ∧
      HEq
        ((runtimeConductorHistoryRoot observation nontrivial
          ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
            ((runtimeConductorHistoryInstallation
              observation nontrivial).embed PUnit.unit)
            step.sourceOccurrence)
        ((runtimeConductorFaithfulMaterialLaw
          observation nontrivial).toProjectionLaw.outcomeAt
            PUnit.unit step.sourceOccurrence) := by
  dsimp only
  refine ⟨RootGeneratedCofinalFaithfulSettlementStepAt.wholeLedgerWriteBack_eq_root _,
    RootGeneratedCofinalFaithfulSettlementStepAt.nextCurrent_eq_root _, ?_⟩
  exact RootGeneratedCofinalFaithfulSettlementStepAt.installedFaithful_factorizes
    (runtimeConductorHistoryStepAt observation nontrivial depth)

/-- Joint relation and effect outcomes are still read through their original
installation paths at the conductor-history root. -/
theorem runtimeConductorHistory_inheritedJointEffect_factorize
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimeConductorHistoryRoot observation nontrivial
    let visit := runtimeConductorHistoryVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    HEq (evolution.generated.projectionOutcome
          ((runtimeJointFaithfulInstallationAtConductorHistoryRoot
            observation nontrivial).embed PUnit.unit))
        ((runtimeJointFaithfulMaterialLaw observation nontrivial
          ).toProjectionLaw.outcomeAt PUnit.unit
            (root.emitted visit.current)) ∧
      HEq (evolution.generated.projectionOutcome
          ((runtimeEffectInstallationAtConductorHistoryRoot
            observation nontrivial).embed PUnit.unit))
        ((runtimeEffectLaw observation nontrivial
          ).toProjectionLaw.outcomeAt PUnit.unit
            (root.emitted visit.current)) := by
  dsimp only
  constructor
  · exact (((runtimeConductorHistoryRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimeConductorHistoryVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimeJointFaithfulInstallationAtConductorHistoryRoot
        observation nontrivial) PUnit.unit).2.1
  · exact (((runtimeConductorHistoryRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimeConductorHistoryVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimeEffectInstallationAtConductorHistoryRoot
        observation nontrivial) PUnit.unit).2.1

end
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
