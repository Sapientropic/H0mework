import H0mework.Realization.JointState.SourceBoundary
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaRootEffect

/-!
# Root-scale and quarter-scale faces of the paired-Omega occurrence

The named runtime needs two sibling action scales.  The existing root scale
drives the installed q-rich balance; the quarter scale is the actual scale of
the expanding Riesz incidence.  Both are generated from the same paired input
and land in the same constant ambient.  This file contains only their actual
values and defining relations; history/ledger installation is downstream.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open SourceGeneratedIntegralCoherentJointAction
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open ThetaJRoleRepresentation
open Character.GlobalCoPoissonCurrent

noncomputable section

/-- Constant ambient shared by both scale faces. -/
abbrev PairedOmegaJointAmbient :=
  IntegralScaleCarrier ×
    ((JointGraphTarget × JointGraphTarget) × QRich.ClozelJPair)

def runtimeJointInputAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :=
  pairedJointInput observation nontrivial (stageSqrtScaleUnit stage)

def runtimeJointEvolvedAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointInputAt observation nontrivial stage
  (input.omega (input.seedLift (delta 1))).1

def runtimeJointSourceSeedAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointInputAt observation nontrivial stage
  (input.seedLift (delta 1)).1

def runtimeJointSourceActionAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointInputAt observation nontrivial stage
  (input.seedLift (input.integralAction (delta 1))).1

def runtimeJointIncidenceAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointInputAt observation nontrivial stage
  (input.incidenceResidual (delta 1)).1

def runtimeJointSourceBoundaryAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointInputAt observation nontrivial stage
  (input.sourceBoundary (delta 1)).1

theorem runtimeJointAmbient_sourceBoundary_relation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointSourceSeedAmbientAt observation nontrivial stage -
      runtimeJointSourceActionAmbientAt observation nontrivial stage -
      runtimeJointSourceBoundaryAmbientAt observation nontrivial stage = 0 := by
  let input := runtimeJointInputAt observation nontrivial stage
  have relation :
      input.seedLift (delta 1) -
          input.seedLift (input.integralAction (delta 1)) -
        input.sourceBoundary (delta 1) = 0 := by
    rw [Input.sourceBoundary]
    abel
  exact congrArg Subtype.val relation

theorem runtimeJointAmbient_incidence_relation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointEvolvedAmbientAt observation nontrivial stage -
      runtimeJointSourceActionAmbientAt observation nontrivial stage -
      runtimeJointIncidenceAmbientAt observation nontrivial stage = 0 := by
  let input := runtimeJointInputAt observation nontrivial stage
  have relation :
      input.omega (input.seedLift (delta 1)) -
          input.seedLift (input.integralAction (delta 1)) -
        input.incidenceResidual (delta 1) = 0 := by
    rw [Input.incidenceResidual]
    abel
  exact congrArg Subtype.val relation

/-- Fourth-root action scale attached to the same compiler stage. -/
def runtimeJointQuarterScaleUnit (stage : Nat) : Units NNReal :=
  positiveRealUnit
    (Real.sqrt (positiveUnitValue (stageSqrtScaleUnit stage)))
    (Real.sqrt_pos.2 (positiveUnitValue_pos (stageSqrtScaleUnit stage)))

theorem runtimeJointQuarterScaleUnit_zero :
    runtimeJointQuarterScaleUnit 0 = stageZeroQuarterScaleUnit := by
  apply Units.ext
  apply NNReal.eq
  simp only [runtimeJointQuarterScaleUnit, stageZeroQuarterScaleUnit,
    positiveRealUnit_val]
  rw [stageZeroSqrtScale_unit_value]

def runtimeJointQuarterInputAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :=
  pairedJointInput observation nontrivial (runtimeJointQuarterScaleUnit stage)

def runtimeJointQuarterEvolvedAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointQuarterInputAt observation nontrivial stage
  (input.omega (input.seedLift (delta 1))).1

def runtimeJointQuarterSourceSeedAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointQuarterInputAt observation nontrivial stage
  (input.seedLift (delta 1)).1

def runtimeJointQuarterSourceActionAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointQuarterInputAt observation nontrivial stage
  (input.seedLift (input.integralAction (delta 1))).1

def runtimeJointQuarterIncidenceAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointQuarterInputAt observation nontrivial stage
  (input.incidenceResidual (delta 1)).1

def runtimeJointQuarterSourceBoundaryAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let input := runtimeJointQuarterInputAt observation nontrivial stage
  (input.sourceBoundary (delta 1)).1

/-- Energy-only projection of one graph target.  The measurement coordinate
is retained by the complementary remainder below. -/
def graphEnergyOnly (state : JointGraphTarget) : JointGraphTarget :=
  (WithLp.linearEquiv 2 ℂ
    (PositiveMellinQuarterEnergy × ℂ)).symm (state.fst, 0)

@[simp] theorem graphEnergyOnly_fst (state : JointGraphTarget) :
    (graphEnergyOnly state).fst = state.fst :=
  rfl

@[simp] theorem graphEnergyOnly_snd (state : JointGraphTarget) :
    (graphEnergyOnly state).snd = 0 :=
  rfl

def pairedGraphEnergyOnly
    (state : JointGraphTarget × JointGraphTarget) :
    JointGraphTarget × JointGraphTarget :=
  (graphEnergyOnly state.1, graphEnergyOnly state.2)

/-- Canonical energy coordinate of the actual quarter source boundary in the
existing joint ambient. -/
def runtimeJointQuarterBoundaryEnergyAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  let boundary := runtimeJointQuarterSourceBoundaryAmbientAt
    observation nontrivial stage
  (0, (pairedGraphEnergyOnly boundary.2.1, 0))

/-- Everything not stored in the energy-only coordinate: integral boundary,
graph measurements and the existing q-rich read. -/
def runtimeJointQuarterBoundaryRemainderAmbientAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : PairedOmegaJointAmbient :=
  runtimeJointQuarterSourceBoundaryAmbientAt observation nontrivial stage -
    runtimeJointQuarterBoundaryEnergyAmbientAt observation nontrivial stage

theorem runtimeJointQuarterAmbient_boundaryEnergy_relation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointQuarterSourceBoundaryAmbientAt observation nontrivial stage -
      runtimeJointQuarterBoundaryEnergyAmbientAt observation nontrivial stage -
      runtimeJointQuarterBoundaryRemainderAmbientAt
        observation nontrivial stage = 0 := by
  simp [runtimeJointQuarterBoundaryRemainderAmbientAt]

/-- The existing root-effect coordinates evaluated at the sibling quarter
scale.  These are dependent faces of the same occurrence, not a second effect
source. -/
def runtimeJointQuarterPhaseAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : QRich.ClozelJPair :=
  pairedRootPhaseResidual observation nontrivial
    (runtimeJointQuarterScaleUnit stage)

def runtimeJointQuarterRetainedAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : QRich.ClozelJPair :=
  pairedOmegaMeasurementResidual observation nontrivial
    (runtimeJointQuarterScaleUnit stage)

def runtimeJointQuarterCenteredTraceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : QRich.ClozelJPair :=
  pairedRootCenteredTrace observation nontrivial
    (runtimeJointQuarterScaleUnit stage)

theorem runtimeJointQuarterAmbient_sourceBoundary_relation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointQuarterSourceSeedAmbientAt observation nontrivial stage -
      runtimeJointQuarterSourceActionAmbientAt observation nontrivial stage -
      runtimeJointQuarterSourceBoundaryAmbientAt
        observation nontrivial stage = 0 := by
  let input := runtimeJointQuarterInputAt observation nontrivial stage
  have relation :
      input.seedLift (delta 1) -
          input.seedLift (input.integralAction (delta 1)) -
        input.sourceBoundary (delta 1) = 0 := by
    rw [Input.sourceBoundary]
    abel
  exact congrArg Subtype.val relation

theorem runtimeJointQuarterAmbient_incidence_relation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointQuarterEvolvedAmbientAt observation nontrivial stage -
      runtimeJointQuarterSourceActionAmbientAt observation nontrivial stage -
      runtimeJointQuarterIncidenceAmbientAt observation nontrivial stage = 0 := by
  let input := runtimeJointQuarterInputAt observation nontrivial stage
  have relation :
      input.omega (input.seedLift (delta 1)) -
          input.seedLift (input.integralAction (delta 1)) -
        input.incidenceResidual (delta 1) = 0 := by
    rw [Input.incidenceResidual]
    abel
  exact congrArg Subtype.val relation

theorem runtimeJointQuarterEffect_conservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointQuarterPhaseAt observation nontrivial stage =
      runtimeJointQuarterRetainedAt observation nontrivial stage +
        runtimeJointQuarterCenteredTraceAt observation nontrivial stage := by
  exact pairedRootPhaseResidual_eq_incidence_add_centeredTrace
    observation nontrivial (runtimeJointQuarterScaleUnit stage)

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
