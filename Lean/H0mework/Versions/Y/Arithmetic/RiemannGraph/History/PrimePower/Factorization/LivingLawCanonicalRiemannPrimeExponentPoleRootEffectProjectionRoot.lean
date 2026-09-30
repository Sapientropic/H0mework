import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleEnergyCoimageRoot
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleRootEffectProjection

/-!
# Fixed-root activation of the prime-exponent Riesz effect projection

Every actual positive prime-power receipt now exposes the installed phase,
its Riesz-energy component, the scalar vertical trace, and the inherited
centered trace.  This complete receipt-indexed face is installed above the
energy coimage without changing the source emitter, whole ledger, or next.
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
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

noncomputable section

structure GeneratedPrimeExponentPoleRootEffectValue where
  phase : QRich.ClozelJPair
  energy : QRich.ClozelJPair
  verticalTrace : QRich.ClozelJPair
  centeredTrace : QRich.ClozelJPair

abbrev GeneratedPrimeExponentPoleRootEffectFaceAt :=
  ConductorPrimePowerIndex → GeneratedPrimeExponentPoleRootEffectValue

def generatedPrimeExponentPoleRootEffectFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GeneratedPrimeExponentPoleRootEffectFaceAt :=
  fun index =>
    let stage := PrimePower.Runtime.primePowerRuntimeStage
      index.1 index.2.1
    { phase :=
        (installedRuntimeEffectValueAt observation nontrivial stage).phase
      energy := pairedPrimeExponentPoleBoundaryRieszEnergy
        observation nontrivial index
      verticalTrace := pairedPrimeExponentPoleBoundaryVerticalTrace
        observation nontrivial index
      centeredTrace :=
        (installedRuntimeEffectValueAt
          observation nontrivial stage).centeredTrace }

theorem generatedPrimeExponentPoleRootEffectFace_conservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    let value := generatedPrimeExponentPoleRootEffectFace
      observation nontrivial index
    value.phase = value.energy + value.verticalTrace + value.centeredTrace := by
  dsimp only [generatedPrimeExponentPoleRootEffectFace]
  exact installedRuntimePrimeExponentPole_phase_threeTerm
    observation nontrivial index

def runtimePrimeExponentPoleRootEffectProjectionLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw
      (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
        observation nontrivial).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} _occurrence _active =>
    ULift GeneratedPrimeExponentPoleRootEffectFaceAt
  project := fun _projection {_current} _occurrence _active =>
    ULift.up (generatedPrimeExponentPoleRootEffectFace
      observation nontrivial)

@[simp] theorem runtimePrimeExponentPoleRootEffectProjectionLaw_outcomeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
        observation nontrivial).restructuringSource.source.toRootSource.actual.OccurrenceAt
          current) :
    (runtimePrimeExponentPoleRootEffectProjectionLaw
      observation nontrivial).outcomeAt PUnit.unit occurrence =
        .inl ⟨PUnit.unit,
          ULift.up (generatedPrimeExponentPoleRootEffectFace
            observation nontrivial)⟩ :=
  rfl

def runtimePrimeExponentPoleRootEffectAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
    observation nontrivial).withProjectionCoface
      (runtimePrimeExponentPoleRootEffectProjectionLaw
        observation nontrivial)

def runtimePrimeExponentPoleRootEffectLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimePrimeExponentPoleRootEffectAuthoritySource
    observation nontrivial
  terminalHandoff :=
    (runtimePrimeExponentPoleRootEffectAuthoritySource
      observation nontrivial).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimePrimeExponentPoleRootEffectRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimePrimeExponentPoleRootEffectLivingSource
    observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimePrimeExponentPoleRootEffectRoot_reuses_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimePrimeExponentPoleRootEffectRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimePrimeExponentPoleRootEffectRoot observation nontrivial
        ).emitted = emitted :=
  ⟨rfl, rfl⟩

def runtimePrimeExponentPoleRootEffectInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleRootEffectProjectionLaw observation nontrivial)
      (runtimePrimeExponentPoleRootEffectAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
      observation nontrivial)
    (runtimePrimeExponentPoleRootEffectProjectionLaw observation nontrivial)

def runtimePrimeExponentPoleRootEffectInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
        observation nontrivial).projectionLaw
      (runtimePrimeExponentPoleRootEffectAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimePrimeExponentPoleEnergyCoimageAuthoritySource
      observation nontrivial)
    (runtimePrimeExponentPoleRootEffectProjectionLaw observation nontrivial)

def runtimePrimeExponentPoleEnergyCoimageInstallationAtRootEffectRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleEnergyCoimageProjectionLaw
        observation nontrivial)
      (runtimePrimeExponentPoleRootEffectAuthoritySource
        observation nontrivial).projectionLaw :=
  (runtimePrimeExponentPoleEnergyCoimageInstallation
    observation nontrivial).trans
      (runtimePrimeExponentPoleRootEffectInheritedInstallation
        observation nontrivial)

def runtimePrimeExponentPoleRootEffectVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimePrimeExponentPoleRootEffectRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

theorem runtimePrimeExponentPoleRootEffect_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleRootEffectRoot observation nontrivial
    let visit := runtimePrimeExponentPoleRootEffectVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          ((runtimePrimeExponentPoleRootEffectInstallation
            observation nontrivial).embed PUnit.unit))
        ((runtimePrimeExponentPoleRootEffectProjectionLaw
          observation nontrivial).outcomeAt PUnit.unit
            (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleRootEffectRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleRootEffectVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimePrimeExponentPoleRootEffectInstallation observation nontrivial)
      PUnit.unit

theorem runtimePrimeExponentPoleEnergyCoimage_factorizes_atRootEffectRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleRootEffectRoot observation nontrivial
    let visit := runtimePrimeExponentPoleRootEffectVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    HEq (evolution.generated.projectionOutcome
          ((runtimePrimeExponentPoleEnergyCoimageInstallationAtRootEffectRoot
            observation nontrivial).embed PUnit.unit))
        ((runtimePrimeExponentPoleEnergyCoimageProjectionLaw
          observation nontrivial).outcomeAt PUnit.unit
            (root.emitted visit.current)) := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleRootEffectRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleRootEffectVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimePrimeExponentPoleEnergyCoimageInstallationAtRootEffectRoot
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
