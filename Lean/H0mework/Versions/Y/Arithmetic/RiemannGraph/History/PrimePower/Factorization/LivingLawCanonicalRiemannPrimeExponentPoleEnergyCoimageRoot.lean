import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleCouplingRoot
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleEnergyCoimage

/-!
# Fixed-root activation of the prime-exponent energy coimage

The algebraic energy radical quotient and its unique Mellin factor are a
component coface of the already installed prime-exponent pole coupling.  The
same canonical answer retains the multiplicative/integral parent, whole
ledger, and generated next.
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

def runtimePrimeExponentPoleEnergyCoimageProjectionLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw
      (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} _occurrence _active =>
    ULift (GeneratedPrimeExponentPoleEnergyCoimageFaceAt
      observation nontrivial)
  project := fun _projection {_current} _occurrence _active =>
    ULift.up (generatedPrimeExponentPoleEnergyCoimageFace
      observation nontrivial)

@[simp] theorem runtimePrimeExponentPoleEnergyCoimageProjectionLaw_outcomeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    (runtimePrimeExponentPoleEnergyCoimageProjectionLaw
      observation nontrivial).outcomeAt PUnit.unit occurrence =
        .inl ⟨PUnit.unit,
          ULift.up (generatedPrimeExponentPoleEnergyCoimageFace
            observation nontrivial)⟩ :=
  rfl

def runtimePrimeExponentPoleEnergyCoimageAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimePrimeExponentPoleEnergyCoimageProjectionLaw
        observation nontrivial)

def runtimePrimeExponentPoleEnergyCoimageLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimePrimeExponentPoleEnergyCoimageAuthoritySource
    observation nontrivial
  terminalHandoff :=
    (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
      observation nontrivial).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimePrimeExponentPoleEnergyCoimageRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimePrimeExponentPoleEnergyCoimageLivingSource
    observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimePrimeExponentPoleEnergyCoimageRoot_reuses_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimePrimeExponentPoleEnergyCoimageRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimePrimeExponentPoleEnergyCoimageRoot observation nontrivial
        ).emitted = emitted :=
  ⟨rfl, rfl⟩

def runtimePrimeExponentPoleEnergyCoimageInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleEnergyCoimageProjectionLaw
        observation nontrivial)
      (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial)
    (runtimePrimeExponentPoleEnergyCoimageProjectionLaw
      observation nontrivial)

def runtimePrimeExponentPoleEnergyCoimageInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial
        ).projectionLaw
      (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimePrimeExponentPoleCouplingAuthoritySource observation nontrivial)
    (runtimePrimeExponentPoleEnergyCoimageProjectionLaw
      observation nontrivial)

def runtimePrimeExponentPoleCouplingInstallationAtEnergyCoimageRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleCouplingProjectionLaw observation nontrivial)
      (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
        observation nontrivial).projectionLaw :=
  (runtimePrimeExponentPoleCouplingInstallation observation nontrivial).trans
    (runtimePrimeExponentPoleEnergyCoimageInheritedInstallation
      observation nontrivial)

def runtimePrimeExponentPoleEnergyCoimageVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimePrimeExponentPoleEnergyCoimageRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

theorem runtimePrimeExponentPoleEnergyCoimage_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleEnergyCoimageRoot
      observation nontrivial
    let visit := runtimePrimeExponentPoleEnergyCoimageVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          ((runtimePrimeExponentPoleEnergyCoimageInstallation
            observation nontrivial).embed PUnit.unit))
        ((runtimePrimeExponentPoleEnergyCoimageProjectionLaw
          observation nontrivial).outcomeAt PUnit.unit
            (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleEnergyCoimageRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleEnergyCoimageVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimePrimeExponentPoleEnergyCoimageInstallation
        observation nontrivial)
      PUnit.unit

theorem runtimePrimeExponentPoleCoupling_factorizes_atEnergyCoimageRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleEnergyCoimageRoot
      observation nontrivial
    let visit := runtimePrimeExponentPoleEnergyCoimageVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    HEq (evolution.generated.projectionOutcome
          ((runtimePrimeExponentPoleCouplingInstallationAtEnergyCoimageRoot
            observation nontrivial).embed PUnit.unit))
        ((runtimePrimeExponentPoleCouplingProjectionLaw
          observation nontrivial).outcomeAt PUnit.unit
            (root.emitted visit.current)) := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleEnergyCoimageRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleEnergyCoimageVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimePrimeExponentPoleCouplingInstallationAtEnergyCoimageRoot
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
