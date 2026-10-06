import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Arithmetic.PrimeLeakage.AllPlaceWeilRuntimeMaterial

/-!
# Root installation of the all-place Weil state

The occurrence-sensitive Euler--Weil state is adjoined as a projection
coface of the faithful joint runtime before emission.  The joint relation,
effect history, source emitter, whole ledger, and generated next remain the
inherited root mechanisms.
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
namespace Root

open CanonicalUnitArithmeticRoot
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open Material

noncomputable section

def runtimeAllPlaceWeilAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeJointFaithfulAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimeAllPlaceWeilProjectionLaw observation nontrivial)

def runtimeAllPlaceWeilLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimeAllPlaceWeilAuthoritySource observation nontrivial
  terminalHandoff :=
    (runtimeAllPlaceWeilAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimeAllPlaceWeilRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimeAllPlaceWeilLivingSource observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimeAllPlaceWeilRoot_reuses_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeAllPlaceWeilRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimeAllPlaceWeilRoot observation nontrivial).emitted = emitted := by
  exact ⟨rfl, rfl⟩

def runtimeAllPlaceWeilInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeAllPlaceWeilProjectionLaw observation nontrivial)
      (runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimeJointFaithfulAuthoritySource observation nontrivial)
    (runtimeAllPlaceWeilProjectionLaw observation nontrivial)

def runtimeAllPlaceWeilInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeJointFaithfulAuthoritySource observation nontrivial).projectionLaw
      (runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimeJointFaithfulAuthoritySource observation nontrivial)
    (runtimeAllPlaceWeilProjectionLaw observation nontrivial)

def runtimeJointFaithfulInstallationAtAllPlaceWeilRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeJointFaithfulInstallation observation nontrivial).trans
    (runtimeAllPlaceWeilInheritedInstallation observation nontrivial)

def runtimeEffectInstallationAtAllPlaceWeilRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectLaw observation nontrivial).toProjectionLaw
      (runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeEffectInstallationAtJointRoot observation nontrivial).trans
    (runtimeAllPlaceWeilInheritedInstallation observation nontrivial)

def runtimeAllPlaceWeilVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimeAllPlaceWeilRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

theorem runtimeAllPlaceWeil_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimeAllPlaceWeilRoot observation nontrivial
    let visit := runtimeAllPlaceWeilVisitAt observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          ((runtimeAllPlaceWeilInstallation observation nontrivial
            ).embed PUnit.unit))
        ((runtimeAllPlaceWeilProjectionLaw observation nontrivial
          ).outcomeAt PUnit.unit (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  exact
    ((runtimeAllPlaceWeilRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimeAllPlaceWeilVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimeAllPlaceWeilInstallation observation nontrivial)
      PUnit.unit

end
end Root
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
