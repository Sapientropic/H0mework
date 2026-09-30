import H0mework.Realization.Integral.GroupRingPairing
import H0mework.Realization.Coherent.PerfectRealization
import H0mework.Versions.Y.Arithmetic.SonineGap.ClozelIntegralGraphRadialDisposition

/-!
# Perfect realization of the zero-owned integral graph orbit

The integral scale group ring carries its canonical Kronecker evaluation.
Selected and reversal graph orbits therefore descend through the same
source-generated perfect carrier, and their existing coherent covariance
residuals are recovered verbatim on source events.  The outer
representation-residual branch is impossible here because the Kronecker
evaluation is faithful; no critical-line or residual-zero premise is used.
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

open Character.GlobalCoPoissonCurrent
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralEquivariantPerfectRealization
open SourceGeneratedIntegralGroupRingPerfectPair
open SourceGeneratedIntegralCoherentCovariance
open ThetaJRoleRepresentation

noncomputable section

/-- Source-generated discrete pairing on the actual positive-scale charge
carrier. -/
abbrev integralScalePerfectEvaluation :
    IntegralScaleCarrier →ₗ[ℤ] Module.Dual ℤ IntegralScaleCarrier :=
  SourceGeneratedIntegralGroupRingPerfectPair.evaluation
    (G := Units NNReal)

theorem selectedIntegralGraphOrbit_kernel_compatible
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    LinearMap.ker integralScalePerfectEvaluation ≤
      LinearMap.ker (selectedIntegralGraphOrbit observation nontrivial) := by
  rw [SourceGeneratedIntegralGroupRingPerfectPair.evaluation_ker_eq_bot]
  exact bot_le

theorem reversalIntegralGraphOrbit_kernel_compatible
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    LinearMap.ker integralScalePerfectEvaluation ≤
      LinearMap.ker (reversalIntegralGraphOrbit observation nontrivial) := by
  rw [SourceGeneratedIntegralGroupRingPerfectPair.evaluation_ker_eq_bot]
  exact bot_le

/-- Selected and reversal measurements share this one source translation and
owner-free graph evolution. -/
def integralGraphJointAction (scale : Units NNReal) :
    JointActionData (H := JointGraphTarget) integralScalePerfectEvaluation where
  sourceAction :=
    SourceGeneratedIntegralGroupRingPerfectPair.translationAction scale
  coherentEvolution :=
    (positiveMellinQuarterGraphTargetIsometry
      (Real.log (scaleSquare scale))).toLinearIsometry

def selectedIntegralGraphPerfectFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    RealizedFace integralScalePerfectEvaluation
      (selectedIntegralGraphOrbit observation nontrivial)
      (integralGraphJointAction scale) :=
  generateRealizedFace integralScalePerfectEvaluation
    (selectedIntegralGraphOrbit observation nontrivial)
    (integralGraphJointAction scale)
    (selectedIntegralGraphOrbit_kernel_compatible observation nontrivial)

def reversalIntegralGraphPerfectFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    RealizedFace integralScalePerfectEvaluation
      (reversalIntegralGraphOrbit observation nontrivial)
      (integralGraphJointAction scale) :=
  generateRealizedFace integralScalePerfectEvaluation
    (reversalIntegralGraphOrbit observation nontrivial)
    (integralGraphJointAction scale)
    (reversalIntegralGraphOrbit_kernel_compatible observation nontrivial)

/-- Selected perfect-realization residual reads the already generated actual
owner-free coupling residual on every integral event. -/
theorem selectedIntegralGraphPerfect_couplingResidual_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    couplingResidual
        (perfectCovarianceAction integralScalePerfectEvaluation
          (integralGraphJointAction scale)
          (selectedIntegralGraphPerfectFace observation nontrivial scale).readout)
        (SourceGeneratedScalarPerfectification.canonicalMap
          integralScalePerfectEvaluation event) =
      selectedOwnerFreeCouplingResidual observation nontrivial scale event := by
  rw [couplingResidual_source_readback integralScalePerfectEvaluation
    (selectedIntegralGraphOrbit observation nontrivial)
    (integralGraphJointAction scale)
    (selectedIntegralGraphPerfectFace observation nontrivial scale).readout
    (selectedIntegralGraphPerfectFace observation nontrivial scale).source_readback]
  exact selectedIntegralGraphCovariance_couplingResidual
    observation nontrivial scale event

/-- Reversal is a sibling measurement of the same perfect carrier. -/
theorem reversalIntegralGraphPerfect_couplingResidual_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    couplingResidual
        (perfectCovarianceAction integralScalePerfectEvaluation
          (integralGraphJointAction scale)
          (reversalIntegralGraphPerfectFace observation nontrivial scale).readout)
        (SourceGeneratedScalarPerfectification.canonicalMap
          integralScalePerfectEvaluation event) =
      reversalOwnerFreeCouplingResidual observation nontrivial scale event := by
  rw [couplingResidual_source_readback integralScalePerfectEvaluation
    (reversalIntegralGraphOrbit observation nontrivial)
    (integralGraphJointAction scale)
    (reversalIntegralGraphPerfectFace observation nontrivial scale).readout
    (reversalIntegralGraphPerfectFace observation nontrivial scale).source_readback]
  exact reversalIntegralGraphCovariance_couplingResidual
    observation nontrivial scale event

/-- The perfect-carrier radial coordinate is exactly the already certified
source-event radial coordinate. -/
theorem selectedIntegralGraphPerfect_radialResidual_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    radialResidual
        (perfectCovarianceAction integralScalePerfectEvaluation
          (integralGraphJointAction scale)
          (selectedIntegralGraphPerfectFace observation nontrivial scale).readout)
        (SourceGeneratedScalarPerfectification.canonicalMap
          integralScalePerfectEvaluation event) =
      radialResidual
        (selectedIntegralGraphCovarianceAction
          observation nontrivial scale) event := by
  rw [radialResidual_source_readback integralScalePerfectEvaluation
    (selectedIntegralGraphOrbit observation nontrivial)
    (integralGraphJointAction scale)
    (selectedIntegralGraphPerfectFace observation nontrivial scale).readout
    (selectedIntegralGraphPerfectFace observation nontrivial scale).source_readback]
  unfold radialResidual selectedIntegralGraphCovarianceAction
  rw [LinearIsometry.norm_map]
  rfl

/-- At the actual stage-zero charge, the universal perfect realization has
the same zero fibre as the critical-line coordinate. -/
theorem selectedIntegralGraphPerfect_stageZero_radial_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    radialResidual
        (perfectCovarianceAction integralScalePerfectEvaluation
          (integralGraphJointAction (stageSqrtScaleUnit 0))
          (selectedIntegralGraphPerfectFace observation nontrivial
            (stageSqrtScaleUnit 0)).readout)
        (SourceGeneratedScalarPerfectification.canonicalMap
          integralScalePerfectEvaluation (delta 1)) = 0 ↔
      observation.coordinate.re = 1 / 2 := by
  rw [selectedIntegralGraphPerfect_radialResidual_readback]
  exact selectedIntegralGraphCovariance_radialResidual_delta_one_eq_zero_iff
    observation nontrivial

theorem selectedIntegralGraphPerfect_settlement_is_realized
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    ∃ face,
      settleRealization integralScalePerfectEvaluation
          (selectedIntegralGraphOrbit observation nontrivial)
          (integralGraphJointAction scale) =
        RealizationDisposition.realized face := by
  generalize outcomeEq :
      settleRealization integralScalePerfectEvaluation
        (selectedIntegralGraphOrbit observation nontrivial)
        (integralGraphJointAction scale) = outcome
  cases outcome with
  | realized face => exact ⟨face, rfl⟩
  | representationResidual coordinate =>
      exfalso
      have invisible := coordinate.invisible_to_dual
      rw [SourceGeneratedIntegralGroupRingPerfectPair.evaluation_ker_eq_bot,
        Submodule.mem_bot] at invisible
      exact coordinate.visible_to_actual (by simp [invisible])

theorem reversalIntegralGraphPerfect_settlement_is_realized
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    ∃ face,
      settleRealization integralScalePerfectEvaluation
          (reversalIntegralGraphOrbit observation nontrivial)
          (integralGraphJointAction scale) =
        RealizationDisposition.realized face := by
  generalize outcomeEq :
      settleRealization integralScalePerfectEvaluation
        (reversalIntegralGraphOrbit observation nontrivial)
        (integralGraphJointAction scale) = outcome
  cases outcome with
  | realized face => exact ⟨face, rfl⟩
  | representationResidual coordinate =>
      exfalso
      have invisible := coordinate.invisible_to_dual
      rw [SourceGeneratedIntegralGroupRingPerfectPair.evaluation_ker_eq_bot,
        Submodule.mem_bot] at invisible
      exact coordinate.visible_to_actual (by simp [invisible])

end

end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
