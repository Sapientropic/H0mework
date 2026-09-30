import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaJointRelationOccurrence
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaEffectRelationOccurrence

/-! Installed-runtime comparison for the source-generated joint relation. -/

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
open ThetaJRoleRepresentation
open Character.GlobalCoPoissonCurrent

noncomputable section

def runtimeEffectGeneratorToJointGenerator :
    RuntimeEffectRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .phase)
  | (stage, .retained) => (stage, .retained)
  | (stage, .centeredTrace) => (stage, .centeredTrace)

def runtimeEffectRelationToJointRelation :
    (RuntimeEffectRelationGenerator →₀ ℤ) →ₗ[ℤ]
      (RuntimeJointRelationGenerator →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ runtimeEffectGeneratorToJointGenerator

@[simp] theorem runtimeEffectRelationToJointRelation_stage
    (stage : Nat) :
    runtimeEffectRelationToJointRelation (runtimeEffectStageRelation stage) =
      runtimeJointBalanceStageRelation stage := by
  simp [runtimeEffectRelationToJointRelation,
    runtimeEffectGeneratorToJointGenerator, runtimeEffectStageRelation,
    runtimeJointBalanceStageRelation, runtimeEffectRelationAtom,
    runtimeJointRelationAtom, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_sub]

/-- The old detector evaluator is literally the balance summand of the new
full evaluator. -/
theorem runtimeJointRelationEvaluator_extends_detector
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeJointBalanceFace.comp
        (runtimeJointRelationEvaluator observation nontrivial)).comp
          runtimeEffectRelationToJointRelation =
      runtimeEffectRelationEvaluator observation nontrivial := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  rcases generator with ⟨stage, role⟩
  cases role <;>
    simp [runtimeJointBalanceFace, runtimeJointRelationEvaluator,
      runtimeEffectRelationEvaluator, runtimeEffectRelationToJointRelation,
      runtimeEffectGeneratorToJointGenerator,
      runtimeJointRelationGeneratorValue,
      runtimeEffectRelationGeneratorValue, runtimeJointBalanceInclusion,
      Finsupp.lmapDomain_apply]

/-- The retained field of the installed stage is the same actual incidence
measurement used above. -/
theorem installedRuntimeEffectValueAt_retained_eq_jointIncidence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (installedRuntimeEffectValueAt observation nontrivial stage).retained =
      pairedOmegaMeasurementResidual observation nontrivial
        (stageSqrtScaleUnit stage) := by
  rw [installedRuntimeEffectValueAt_eq_current]
  simp [generateRuntimeEffect]

/-- The two formerly separate mouths meet on an actual value: measurement
of the joint incidence atom is the installed retained effect. -/
theorem runtimeJointIncidence_measurement_eq_installedRetained
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (stage, .incidence)) =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained := by
  change
    (runtimeJointIncidenceAmbientAt observation nontrivial stage).2.2 + 0 =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained
  rw [add_zero]
  change
    pairedOmegaMeasurementResidual observation nontrivial
        (stageSqrtScaleUnit stage) =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained
  exact (installedRuntimeEffectValueAt_retained_eq_jointIncidence
    observation nontrivial stage).symm

/-- With the installed identity measurement action, the nonzero integral
source boundary has the same q-rich read as the vertical incidence. -/
theorem runtimeJointSourceBoundary_measurement_eq_installedRetained
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (stage, .sourceBoundary)) =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained := by
  change
    (runtimeJointInputAt observation nontrivial stage).measurementFace
        ((runtimeJointInputAt observation nontrivial stage).sourceBoundary
          (delta 1)) + 0 = _
  rw [add_zero]
  rw [Input.sourceBoundary_measurement_eq_incidence]
  · change pairedOmegaMeasurementResidual observation nontrivial
        (stageSqrtScaleUnit stage) = _
    exact (installedRuntimeEffectValueAt_retained_eq_jointIncidence
      observation nontrivial stage).symm
  · rfl

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
