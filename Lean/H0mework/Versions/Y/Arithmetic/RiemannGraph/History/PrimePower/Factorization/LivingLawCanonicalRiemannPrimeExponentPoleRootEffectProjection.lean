import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleRieszEnergyVerticalSplit
import H0mework.Versions.Y.Arithmetic.PrimeLeakage.PrimePowerRuntimeAlignment
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaRootEffect
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaFiniteEffectHistory

/-!
# Prime-exponent pole projection of the installed root effect

Every positive prime-power factorization boundary is the retained paired
Omega incidence at its compiler-generated q-rich stage.  The already
generated Riesz energy/vertical split therefore turns the installed phase
row into a three-term conservation law.  No term is assumed or forced to
vanish here.
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
namespace PrimePowerCurrent

open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

/-- Selected/reversal Mellin reads of one actual prime-power boundary. -/
def pairedPrimeExponentPoleBoundaryMellin
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) : QRich.ClozelJPair :=
  (selectedPrimeExponentPoleMellinMap observation nontrivial
      (factorizationBoundaryValue index),
    reversalPrimeExponentPoleMellinMap observation nontrivial
      (factorizationBoundaryValue index))

/-- Root-owned Riesz-energy coordinates of the same boundary. -/
def pairedPrimeExponentPoleBoundaryRieszEnergy
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) : QRich.ClozelJPair :=
  (selectedPrimeExponentPoleRieszEnergyPair observation nontrivial
      (factorizationBoundaryValue index),
    reversalPrimeExponentPoleRieszEnergyPair observation nontrivial
      (factorizationBoundaryValue index))

/-- Scalar vertical coordinates of the same boundary. -/
def pairedPrimeExponentPoleBoundaryVerticalTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) : QRich.ClozelJPair :=
  (selectedPrimeExponentPoleVerticalScalarTrace observation nontrivial
      (factorizationBoundaryValue index),
    reversalPrimeExponentPoleVerticalScalarTrace observation nontrivial
      (factorizationBoundaryValue index))

theorem pairedPrimeExponentPoleBoundaryMellin_verticalSplit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    pairedPrimeExponentPoleBoundaryMellin observation nontrivial index =
      pairedPrimeExponentPoleBoundaryRieszEnergy
          observation nontrivial index +
        pairedPrimeExponentPoleBoundaryVerticalTrace
          observation nontrivial index := by
  apply Prod.ext
  · change selectedPrimeExponentPoleMellinMap observation nontrivial
        (factorizationBoundaryValue index) =
      selectedPrimeExponentPoleRieszEnergyPair observation nontrivial
          (factorizationBoundaryValue index) +
        selectedPrimeExponentPoleVerticalScalarTrace observation nontrivial
          (factorizationBoundaryValue index)
    exact LinearMap.congr_fun
      (selectedPrimeExponentPoleMellin_verticalSplit
        observation nontrivial) (factorizationBoundaryValue index)
  · change reversalPrimeExponentPoleMellinMap observation nontrivial
        (factorizationBoundaryValue index) =
      reversalPrimeExponentPoleRieszEnergyPair observation nontrivial
          (factorizationBoundaryValue index) +
        reversalPrimeExponentPoleVerticalScalarTrace observation nontrivial
          (factorizationBoundaryValue index)
    exact LinearMap.congr_fun
      (reversalPrimeExponentPoleMellin_verticalSplit
        observation nontrivial) (factorizationBoundaryValue index)

/-- The factorization boundary and the paired Omega retained coordinate are
the same source-generated character difference at `p^k`. -/
theorem pairedPrimeExponentPoleBoundaryMellin_eq_incidence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    pairedPrimeExponentPoleBoundaryMellin observation nontrivial index =
      pairedOmegaMeasurementResidual observation nontrivial
        (primePowerUnit index.1 index.2.1) := by
  rw [pairedOmegaMeasurementResidual_eq]
  apply Prod.ext
  · change selectedPrimeExponentPoleMellinMap observation nontrivial
        (factorizationBoundaryValue index) =
      (selectedOwnerFreeCouplingResidual observation nontrivial
        (primePowerUnit index.1 index.2.1) (delta 1)).snd
    rw [selectedPrimeExponentPoleMellin_boundaryValue,
      selectedOwnerFreeCouplingResidual_delta_snd]
    simp [quarterDilationCharacter, scaleSquare, scaleValue]
  · change reversalPrimeExponentPoleMellinMap observation nontrivial
        (factorizationBoundaryValue index) =
      (reversalOwnerFreeCouplingResidual observation nontrivial
        (primePowerUnit index.1 index.2.1) (delta 1)).snd
    rw [reversalPrimeExponentPoleMellin_boundaryValue,
      reversalOwnerFreeCouplingResidual_delta_snd]
    simp [quarterDilationCharacter, scaleSquare, scaleValue]

/-- Runtime alignment: the retained coordinate is read at the q-rich stage
generated by this positive prime-power receipt. -/
theorem pairedPrimeExponentPoleBoundaryMellin_eq_installedRetained
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    pairedPrimeExponentPoleBoundaryMellin observation nontrivial index =
      pairedOmegaMeasurementResidual observation nontrivial
        (stageSqrtScaleUnit
          (AllPlace.WeilQuadratic.PrimePower.Runtime.primePowerRuntimeStage
            index.1 index.2.1)) := by
  rw [pairedPrimeExponentPoleBoundaryMellin_eq_incidence,
    AllPlace.WeilQuadratic.PrimePower.Runtime.primePowerRuntimeStage_scaleUnit
      index.1 index.2.1 index.2.2]

/-- The installed phase row, projected through the factor boundary, is the
Riesz-energy pair plus the scalar vertical trace plus the already installed
centered trace. -/
theorem pairedPrimeExponentPole_installedPhase_threeTerm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    let stage :=
      AllPlace.WeilQuadratic.PrimePower.Runtime.primePowerRuntimeStage
        index.1 index.2.1
    pairedRootPhaseResidual observation nontrivial
        (stageSqrtScaleUnit stage) =
      pairedPrimeExponentPoleBoundaryRieszEnergy
          observation nontrivial index +
        pairedPrimeExponentPoleBoundaryVerticalTrace
            observation nontrivial index +
          pairedRootCenteredTrace observation nontrivial
            (stageSqrtScaleUnit stage) := by
  dsimp only
  rw [pairedRootPhaseResidual_eq_incidence_add_centeredTrace,
    ← pairedPrimeExponentPoleBoundaryMellin_eq_installedRetained,
    pairedPrimeExponentPoleBoundaryMellin_verticalSplit]

/-- Literal installed-runtime consumer of the same three-term projection. -/
theorem installedRuntimePrimeExponentPole_phase_threeTerm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    let stage :=
      AllPlace.WeilQuadratic.PrimePower.Runtime.primePowerRuntimeStage
        index.1 index.2.1
    (installedRuntimeEffectValueAt observation nontrivial stage).phase =
      pairedPrimeExponentPoleBoundaryRieszEnergy
          observation nontrivial index +
        pairedPrimeExponentPoleBoundaryVerticalTrace
            observation nontrivial index +
          (installedRuntimeEffectValueAt
            observation nontrivial stage).centeredTrace := by
  dsimp only
  rw [installedRuntimeEffectValueAt_eq_current]
  simp only [generateRuntimeEffect, currentEffectStage_finiteVisit]
  exact pairedPrimeExponentPole_installedPhase_threeTerm
    observation nontrivial index

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
