import H0mework.Realization.Coherent.PerfectRealization
import H0mework.Realization.Coherent.CovarianceNaturality

/-!
# Naturality of equivariant perfect realization

A source/evaluation map, an isometric measurement map, and the two actual
action squares induce one morphism between the generated perfect/coherent
systems.  The perfect carrier action, measurement, vector residual, and
radial residual all commute along that same morphism.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralEquivariantPerfectRealization

noncomputable section

universe c d h h'

variable {C : Type c} {C' : Type c} {D : Type d} {D' : Type d}
variable [AddCommGroup C] [AddCommGroup C']
variable [AddCommGroup D] [AddCommGroup D']
variable {H : Type h} {H' : Type h'}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

variable (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)
variable (evaluation' : C' →ₗ[ℤ] Module.Dual ℤ D')
variable (measurement : C →ₗ[ℤ] H)
variable (measurement' : C' →ₗ[ℤ] H')
variable (data : JointActionData (H := H) evaluation)
variable (data' : JointActionData (H := H') evaluation')

/-- One morphism of joint source systems.  Every field is an actual square;
no inverse, surjectivity, finite face, or covariance conclusion is assumed. -/
structure JointActionMorphism where
  sourceMap : C →ₗ[ℤ] C'
  dualMap : D' →ₗ[ℤ] D
  hilbertMap : H →ₗᵢ[ℂ] H'
  evaluation_commutes :
    (SourceGeneratedScalarPerfectification.inducedDualTarget dualMap).comp
      evaluation =
        evaluation'.comp sourceMap
  measurement_commutes :
    (hilbertMap.toLinearMap.restrictScalars ℤ).comp measurement =
      measurement'.comp sourceMap
  transition_commutes :
    sourceMap.comp data.sourceAction.carrierAction =
      data'.sourceAction.carrierAction.comp sourceMap
  evolution_commutes :
    hilbertMap.toLinearMap.comp data.coherentEvolution.toLinearMap =
      data'.coherentEvolution.toLinearMap.comp hilbertMap.toLinearMap

/-- Canonical map between the two generated perfect carriers. -/
def perfectCarrierMap
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data') :
    PerfectCarrier evaluation →ₗ[ℤ] PerfectCarrier evaluation' :=
  SourceGeneratedScalarPerfectification.inducedPerfectificationMap
    evaluation evaluation' morphism.sourceMap morphism.dualMap
      morphism.evaluation_commutes

@[simp] theorem perfectCarrierMap_source_readback
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data') :
    (perfectCarrierMap evaluation evaluation' measurement measurement' data
      data' morphism).comp
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation) =
      (SourceGeneratedScalarPerfectification.canonicalMap evaluation').comp
        morphism.sourceMap :=
  SourceGeneratedScalarPerfectification.inducedPerfectificationMap_comp
    evaluation evaluation' morphism.sourceMap morphism.dualMap
      morphism.evaluation_commutes

/-- An outer measurement-factorization residual transports along the same
source/evaluation/measurement morphism.  Isometry injectivity prevents its
visible coordinate from being erased. -/
def representationResidualMap
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data')
    (coordinate :
      SourceGeneratedScalarPerfectification.FaithfulFactorizationResidual
        evaluation measurement) :
    SourceGeneratedScalarPerfectification.FaithfulFactorizationResidual
      evaluation' measurement' where
  coordinate := morphism.sourceMap coordinate.coordinate
  invisible_to_dual := by
    have invisible := coordinate.invisible_to_dual
    rw [LinearMap.mem_ker] at invisible ⊢
    have square := LinearMap.congr_fun morphism.evaluation_commutes
      coordinate.coordinate
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at square
    rw [← square, invisible]
    rfl
  visible_to_actual := by
    intro targetZero
    have square := LinearMap.congr_fun morphism.measurement_commutes
      coordinate.coordinate
    change morphism.hilbertMap (measurement coordinate.coordinate) =
      measurement' (morphism.sourceMap coordinate.coordinate) at square
    have imageZero :
        morphism.hilbertMap (measurement coordinate.coordinate) = 0 :=
      square.trans targetZero
    exact coordinate.visible_to_actual
      (morphism.hilbertMap.injective (by simpa using imageZero))

@[simp] theorem representationResidualMap_coordinate
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data')
    (coordinate :
      SourceGeneratedScalarPerfectification.FaithfulFactorizationResidual
        evaluation measurement) :
    (representationResidualMap evaluation evaluation' measurement measurement'
      data data' morphism coordinate).coordinate =
        morphism.sourceMap coordinate.coordinate :=
  rfl

/-- The actual measurement square descends uniquely to the two realized
perfect faces. -/
theorem realizedMeasurement_naturality
    [CompleteSpace H] [CompleteSpace H']
    (face : RealizedFace evaluation measurement data)
    (face' : RealizedFace evaluation' measurement' data')
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data') :
    (morphism.hilbertMap.toLinearMap.restrictScalars ℤ).comp face.readout =
      face'.readout.comp
        (perfectCarrierMap evaluation evaluation' measurement measurement'
          data data' morphism) := by
  apply LinearMap.ext
  intro value
  obtain ⟨event, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) value
  have sourceReadback := LinearMap.congr_fun face.source_readback event
  have targetReadback := LinearMap.congr_fun face'.source_readback
    (morphism.sourceMap event)
  have measurementSquare := LinearMap.congr_fun morphism.measurement_commutes
    event
  change morphism.hilbertMap (measurement event) =
    measurement' (morphism.sourceMap event) at measurementSquare
  have perfectMapReadback := LinearMap.congr_fun
    (perfectCarrierMap_source_readback evaluation evaluation' measurement
      measurement' data data' morphism) event
  change morphism.hilbertMap
      (face.readout
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation event)) =
    face'.readout
      (perfectCarrierMap evaluation evaluation' measurement measurement' data
        data' morphism
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation event))
  calc
    _ = morphism.hilbertMap (measurement event) :=
      congrArg morphism.hilbertMap sourceReadback
    _ = measurement' (morphism.sourceMap event) := by
      simpa only [LinearMap.comp_apply] using measurementSquare
    _ = face'.readout
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation'
          (morphism.sourceMap event)) := targetReadback.symm
    _ = _ := congrArg face'.readout perfectMapReadback.symm

/-- The source transition square descends to the generated perfect actions. -/
theorem perfectCarrierAction_naturality
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data') :
    (perfectCarrierMap evaluation evaluation' measurement measurement' data
      data' morphism).comp
        (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
          evaluation data.sourceAction) =
      (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
        evaluation' data'.sourceAction).comp
        (perfectCarrierMap evaluation evaluation' measurement measurement'
          data data' morphism) := by
  apply LinearMap.ext
  intro value
  obtain ⟨event, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) value
  have sourceActionReadback := LinearMap.congr_fun
    (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction_canonicalMap
      evaluation data.sourceAction) event
  have targetActionReadback := LinearMap.congr_fun
    (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction_canonicalMap
      evaluation' data'.sourceAction)
    (morphism.sourceMap event)
  have mapReadback := LinearMap.congr_fun
    (perfectCarrierMap_source_readback evaluation evaluation' measurement
      measurement' data data' morphism) event
  have nextMapReadback := LinearMap.congr_fun
    (perfectCarrierMap_source_readback evaluation evaluation' measurement
      measurement' data data' morphism)
    (data.sourceAction.carrierAction event)
  have transitionSquare :
      morphism.sourceMap (data.sourceAction.carrierAction event) =
        data'.sourceAction.carrierAction (morphism.sourceMap event) := by
    simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun morphism.transition_commutes event
  change perfectCarrierMap evaluation evaluation' measurement measurement' data
      data' morphism
        (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
          evaluation data.sourceAction
          (SourceGeneratedScalarPerfectification.canonicalMap evaluation event)) =
    SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
      evaluation' data'.sourceAction
      (perfectCarrierMap evaluation evaluation' measurement measurement' data
        data' morphism
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation event))
  calc
    _ = perfectCarrierMap evaluation evaluation' measurement measurement' data
        data' morphism
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation
          (data.sourceAction.carrierAction event)) :=
      congrArg
        (perfectCarrierMap evaluation evaluation' measurement measurement' data
          data' morphism) sourceActionReadback
    _ = SourceGeneratedScalarPerfectification.canonicalMap evaluation'
        (morphism.sourceMap (data.sourceAction.carrierAction event)) :=
      nextMapReadback
    _ = SourceGeneratedScalarPerfectification.canonicalMap evaluation'
        (data'.sourceAction.carrierAction (morphism.sourceMap event)) :=
      congrArg
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation')
        transitionSquare
    _ = SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
        evaluation' data'.sourceAction
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation'
          (morphism.sourceMap event)) := targetActionReadback.symm
    _ = _ := congrArg
      (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
        evaluation' data'.sourceAction) mapReadback.symm

/-- The generated perfect/coherent systems form an existing generic
covariance morphism, so all residual and completion naturality laws apply. -/
def covarianceMorphism
    [CompleteSpace H] [CompleteSpace H']
    (face : RealizedFace evaluation measurement data)
    (face' : RealizedFace evaluation' measurement' data')
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data') :
    SourceGeneratedIntegralCoherentCovariance.ActionMorphism
      (perfectCovarianceAction evaluation data face.readout)
      (perfectCovarianceAction evaluation' data' face'.readout) where
  sourceMap := perfectCarrierMap evaluation evaluation' measurement measurement'
    data data' morphism
  hilbertMap := morphism.hilbertMap
  feature_commutes := realizedMeasurement_naturality evaluation evaluation'
    measurement measurement' data data' face face' morphism
  transition_commutes := perfectCarrierAction_naturality evaluation evaluation'
    measurement measurement' data data' morphism
  evolution_commutes := morphism.evolution_commutes

theorem couplingResidual_naturality
    [CompleteSpace H] [CompleteSpace H']
    (face : RealizedFace evaluation measurement data)
    (face' : RealizedFace evaluation' measurement' data')
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data')
    (value : PerfectCarrier evaluation) :
    morphism.hilbertMap
        (SourceGeneratedIntegralCoherentCovariance.couplingResidual
          (perfectCovarianceAction evaluation data face.readout) value) =
      SourceGeneratedIntegralCoherentCovariance.couplingResidual
        (perfectCovarianceAction evaluation' data' face'.readout)
        (perfectCarrierMap evaluation evaluation' measurement measurement'
          data data' morphism value) :=
  SourceGeneratedIntegralCoherentCovariance.couplingResidual_naturality
    (covarianceMorphism evaluation evaluation' measurement measurement' data
      data' face face' morphism) value

theorem radialResidual_naturality
    [CompleteSpace H] [CompleteSpace H']
    (face : RealizedFace evaluation measurement data)
    (face' : RealizedFace evaluation' measurement' data')
    (morphism : JointActionMorphism evaluation evaluation' measurement
      measurement' data data')
    (value : PerfectCarrier evaluation) :
    SourceGeneratedIntegralCoherentCovariance.radialResidual
        (perfectCovarianceAction evaluation' data' face'.readout)
        (perfectCarrierMap evaluation evaluation' measurement measurement'
          data data' morphism value) =
      SourceGeneratedIntegralCoherentCovariance.radialResidual
        (perfectCovarianceAction evaluation data face.readout) value :=
  SourceGeneratedIntegralCoherentCovariance.radialResidual_naturality
    (covarianceMorphism evaluation evaluation' measurement measurement' data
      data' face face' morphism) value

end

end SourceGeneratedIntegralEquivariantPerfectRealization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
