import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.LivingLawCanonicalRiemannConductorPrimePowerCurrent

/-!
# Fixed-root activation of the conductor prime-power parent

The receipt-sensitive parent is installed as a projection coface of the
existing conductor-history authority.  The lower source, emitter, conductor
history, whole ledger, and generated next are inherited.  This file changes
authority; the current file only constructs the source-owned mathematical
face.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

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
namespace PrimePowerCurrent

open CanonicalUnitArithmeticRoot
open Material

noncomputable section

def runtimeConductorPrimePowerProjectionLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw
      (runtimeConductorHistoryAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} _occurrence _active =>
    ULift (GeneratedConductorPrimePowerFaceAt observation nontrivial)
  project := fun _projection {_current} _occurrence _active =>
    ULift.up (generatedConductorPrimePowerFace observation nontrivial)

@[simp] theorem runtimeConductorPrimePowerProjectionLaw_outcomeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (runtimeConductorHistoryAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    (runtimeConductorPrimePowerProjectionLaw observation nontrivial
      ).outcomeAt PUnit.unit occurrence =
        .inl ⟨PUnit.unit,
          ULift.up (generatedConductorPrimePowerFace
            observation nontrivial)⟩ :=
  rfl

def runtimeConductorPrimePowerAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeConductorHistoryAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimeConductorPrimePowerProjectionLaw observation nontrivial)

def runtimeConductorPrimePowerLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimeConductorPrimePowerAuthoritySource observation nontrivial
  terminalHandoff :=
    (runtimeConductorPrimePowerAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimeConductorPrimePowerRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimeConductorPrimePowerLivingSource observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimeConductorPrimePowerRoot_reuses_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeConductorPrimePowerRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimeConductorPrimePowerRoot observation nontrivial).emitted =
        emitted :=
  ⟨rfl, rfl⟩

def runtimeConductorPrimePowerInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeConductorPrimePowerProjectionLaw observation nontrivial)
      (runtimeConductorPrimePowerAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimeConductorHistoryAuthoritySource observation nontrivial)
    (runtimeConductorPrimePowerProjectionLaw observation nontrivial)

def runtimeConductorPrimePowerInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeConductorHistoryAuthoritySource observation nontrivial
        ).projectionLaw
      (runtimeConductorPrimePowerAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimeConductorHistoryAuthoritySource observation nontrivial)
    (runtimeConductorPrimePowerProjectionLaw observation nontrivial)

def runtimeConductorHistoryInstallationAtPrimePowerRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeConductorFaithfulMaterialLaw
        observation nontrivial).toProjectionLaw
      (runtimeConductorPrimePowerAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeConductorHistoryInstallation observation nontrivial).trans
    (runtimeConductorPrimePowerInheritedInstallation
      observation nontrivial)

def runtimeAllPlaceWeilInstallationAtPrimePowerRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeAllPlaceWeilProjectionLaw observation nontrivial)
      (runtimeConductorPrimePowerAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeAllPlaceWeilInstallationAtConductorHistoryRoot
      observation nontrivial).trans
    (runtimeConductorPrimePowerInheritedInstallation
      observation nontrivial)

def runtimeConductorPrimePowerVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimeConductorPrimePowerRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

/-- The installed parent face, generated whole-ledger image, and next are
one exact root evolution. -/
theorem runtimeConductorPrimePower_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimeConductorPrimePowerRoot observation nontrivial
    let visit := runtimeConductorPrimePowerVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          ((runtimeConductorPrimePowerInstallation observation nontrivial
            ).embed PUnit.unit))
        ((runtimeConductorPrimePowerProjectionLaw observation nontrivial
          ).outcomeAt PUnit.unit (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  exact
    ((runtimeConductorPrimePowerRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimeConductorPrimePowerVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimeConductorPrimePowerInstallation observation nontrivial)
      PUnit.unit

/-- The inherited conductor-history outcome is present in the same generated
answer as the new prime-power parent. -/
theorem runtimeConductorHistory_factorizes_atPrimePowerRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimeConductorPrimePowerRoot observation nontrivial
    let visit := runtimeConductorPrimePowerVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    HEq (evolution.generated.projectionOutcome
          ((runtimeConductorHistoryInstallationAtPrimePowerRoot
            observation nontrivial).embed PUnit.unit))
        ((runtimeConductorFaithfulMaterialLaw observation nontrivial
          ).toProjectionLaw.outcomeAt PUnit.unit
            (root.emitted visit.current)) := by
  dsimp only
  exact
    ((runtimeConductorPrimePowerRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimeConductorPrimePowerVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimeConductorHistoryInstallationAtPrimePowerRoot
        observation nontrivial)
      PUnit.unit |>.2.1

end
end PrimePowerCurrent
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
