import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleOrbitCoupling

/-!
# Fixed-root activation of prime-exponent pole coupling

The multiplicative factorization carrier and its integral/orbit/energy/Mellin
faces are installed as a component coface of the receipt-sensitive conductor
root.  The parent receipt face, conductor history, whole ledger, and next are
inherited unchanged.
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

noncomputable section

def runtimePrimeExponentPoleCouplingProjectionLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw
      (runtimeConductorPrimePowerAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} _occurrence _active =>
    ULift (GeneratedPrimeExponentPoleCouplingFaceAt observation nontrivial)
  project := fun _projection {_current} _occurrence _active =>
    ULift.up (generatedPrimeExponentPoleCouplingFace observation nontrivial)

@[simp] theorem runtimePrimeExponentPoleCouplingProjectionLaw_outcomeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (runtimeConductorPrimePowerAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    (runtimePrimeExponentPoleCouplingProjectionLaw observation nontrivial
      ).outcomeAt PUnit.unit occurrence =
        .inl ⟨PUnit.unit,
          ULift.up (generatedPrimeExponentPoleCouplingFace
            observation nontrivial)⟩ :=
  rfl

def runtimePrimeExponentPoleCouplingAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeConductorPrimePowerAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimePrimeExponentPoleCouplingProjectionLaw observation nontrivial)

def runtimePrimeExponentPoleCouplingLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimePrimeExponentPoleCouplingAuthoritySource
    observation nontrivial
  terminalHandoff :=
    (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimePrimeExponentPoleCouplingRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimePrimeExponentPoleCouplingLivingSource
    observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimePrimeExponentPoleCouplingRoot_reuses_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimePrimeExponentPoleCouplingRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimePrimeExponentPoleCouplingRoot observation nontrivial).emitted =
        emitted :=
  ⟨rfl, rfl⟩

def runtimePrimeExponentPoleCouplingInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleCouplingProjectionLaw observation nontrivial)
      (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimeConductorPrimePowerAuthoritySource observation nontrivial)
    (runtimePrimeExponentPoleCouplingProjectionLaw observation nontrivial)

def runtimePrimeExponentPoleCouplingInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeConductorPrimePowerAuthoritySource observation nontrivial
        ).projectionLaw
      (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimeConductorPrimePowerAuthoritySource observation nontrivial)
    (runtimePrimeExponentPoleCouplingProjectionLaw observation nontrivial)

def runtimeConductorPrimePowerInstallationAtPoleCouplingRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeConductorPrimePowerProjectionLaw observation nontrivial)
      (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeConductorPrimePowerInstallation observation nontrivial).trans
    (runtimePrimeExponentPoleCouplingInheritedInstallation
      observation nontrivial)

def runtimePrimeExponentPoleCouplingVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimePrimeExponentPoleCouplingRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

theorem runtimePrimeExponentPoleCoupling_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleCouplingRoot observation nontrivial
    let visit := runtimePrimeExponentPoleCouplingVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          ((runtimePrimeExponentPoleCouplingInstallation
            observation nontrivial).embed PUnit.unit))
        ((runtimePrimeExponentPoleCouplingProjectionLaw
          observation nontrivial).outcomeAt PUnit.unit
            (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleCouplingRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleCouplingVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimePrimeExponentPoleCouplingInstallation observation nontrivial)
      PUnit.unit

theorem runtimeConductorPrimePower_factorizes_atPoleCouplingRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleCouplingRoot observation nontrivial
    let visit := runtimePrimeExponentPoleCouplingVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    HEq (evolution.generated.projectionOutcome
          ((runtimeConductorPrimePowerInstallationAtPoleCouplingRoot
            observation nontrivial).embed PUnit.unit))
        ((runtimeConductorPrimePowerProjectionLaw observation nontrivial
          ).outcomeAt PUnit.unit (root.emitted visit.current)) := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleCouplingRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleCouplingVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimeConductorPrimePowerInstallationAtPoleCouplingRoot
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
