import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Fields

/-! The same generated scalar jet enters the complete Gauss Euler form, retaining the original independent-dual matter current. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000
namespace SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineCanonicalCauchyState StageNineConnectionSectorSourceBalance
open StageNineP286ActionCauchySplit
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open Stage9C.Material.SpinPair DiracExteriorMatterAction
open TemporalGauge
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def withMatter (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) : StageNineHolonomicConfiguration :=
  ChargedGauss.replaceMatter (configuration potential) matter dual

private theorem scalar_replace (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    generatedVolumeDensity (toContinuumPointField (ChargedGauss.replaceMatter background matter dual) point) *
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField (ChargedGauss.replaceMatter background matter dual) point)
        (pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField (ChargedGauss.replaceMatter background matter dual) point) (temporalTest data)) =
    p286ScalarCurrentCoefficient source background
      (p286TemporalGaugeOneForm (p286CoordinateEquiv data)) point := rfl

private theorem matter_normal (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    matterGaugeConnectionFirstVariationDensity source 0 point
      (toContinuumPointField (ChargedGauss.replaceMatter
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background) matter dual) point)
      (pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField (ChargedGauss.replaceMatter
          (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background) matter dual) point)
        (temporalTest data)) =
    matterGaugeConnectionFirstVariationDensity source 0 point
      (toContinuumPointField (ChargedGauss.replaceMatter background matter dual) point)
      (pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField (ChargedGauss.replaceMatter background matter dual) point) (temporalTest data)) := rfl

theorem scalar_current_zero (potential : Potential) (regular : PotentialDifferentiable potential)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint)
    (data : P286LieBlockData) :
    generatedVolumeDensity (toContinuumPointField (withMatter potential matter dual)
      (canonicalCauchySlicePoint 0 space)) *
      scalarGaugeConnectionKineticFirstVariationDensity Stage10.Runtime.source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField (withMatter potential matter dual) (canonicalCauchySlicePoint 0 space))
        (pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField (withMatter potential matter dual) (canonicalCauchySlicePoint 0 space))
          (temporalTest data)) = 0 := by
  unfold withMatter
  rw [Stage10.Runtime.source_eq, scalar_replace]
  exact normalConstraint_p286ScalarCurrent_temporal_zeroSlice positiveSmoothUnifiedSource
    (TemporalGauge.configuration potential) space (noncharacteristic potential _)
    (current_scalar_differentiable potential _) (scalar_differentiable potential regular _)
    (p286CoordinateEquiv data)

theorem charged_coefficient (potential : Potential) (regular : PotentialDifferentiable potential)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint)
    (data : P286LieBlockData) :
    formNativeChargedGaugeFirstCoefficient Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (withMatter potential matter dual) (canonicalCauchySlicePoint 0 space))
      (temporalTest data) =
      (dual (canonicalCauchySlicePoint 0 space) (Stage9DEF.Compatibility.currentAction 0 data
        (matter (canonicalCauchySlicePoint 0 space)))).re := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [mul_add, scalar_current_zero potential regular, zero_add]
  have native := ChargedGauss.matter_time potential matter dual (canonicalCauchySlicePoint 0 space) data
  rw [Stage10.Runtime.source_eq] at native ⊢
  unfold withMatter configuration
  rw [matter_normal]
  rw [show matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0
      (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (ChargedGauss.replaceMatter (TemporalGauge.configuration potential) matter dual)
        (canonicalCauchySlicePoint 0 space))
      (pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField (ChargedGauss.replaceMatter (TemporalGauge.configuration potential) matter dual)
          (canonicalCauchySlicePoint 0 space)) (temporalTest data)) = _ from native]
  have volume : generatedVolumeDensity (toContinuumPointField
      (ChargedGauss.replaceMatter
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator (TemporalGauge.configuration potential))
        matter dual) (canonicalCauchySlicePoint 0 space)) = lapse := by
    change |(Stage10.Runtime.configuration.coframe _).det| = lapse
    rw [Stage10.Runtime.configuration_eq, actual_coframe,
      Stage9C.Dynamics.Homogeneous.homogeneousCoframe_det, abs_of_pos lapse_pos]
  rw [volume]
  field_simp [lapse_pos.ne']

theorem charged_projection (potential : Potential) (regular : PotentialDifferentiable potential)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint)
    (data : P286LieBlockData) :
    p286CoordinateLiePairing (p286CoordinateEquiv data)
      (formNativeChargedGaugeThreeForm Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField (withMatter potential matter dual) (canonicalCauchySlicePoint 0 space)) 3) =
      (dual (canonicalCauchySlicePoint 0 space) (Stage9DEF.Compatibility.currentAction 0 data
        (matter (canonicalCauchySlicePoint 0 space)))).re := by
  have result := formNativeChargedGaugeThreeForm_evaluation Stage10.Runtime.source 0
    (canonicalCauchySlicePoint 0 space)
    (toContinuumPointField (withMatter potential matter dual) (canonicalCauchySlicePoint 0 space))
    (temporalTest data)
  rw [charged_coefficient potential regular] at result
  have zeroPair (value : P286CoordinateCarrier) : p286CoordinateLiePairing 0 value = 0 := by
    simp [p286CoordinateLiePairing, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]
  simpa [p286GaugeOneFormThreeFormWedgeCoefficient, temporalTest,
    Fin.sum_univ_four, oneWedgeThreeSign, missingTripleOfOneForm, zeroPair] using result

private theorem auxiliary_normal (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
      (ChargedGauss.replaceMatter
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background) matter dual) point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative background point := rfl

theorem auxiliary_preserved (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (withMatter potential matter dual) point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (TemporalGauge.configuration potential) point :=
  auxiliary_normal (TemporalGauge.configuration potential) matter dual point

theorem gauss_projection (potential : Potential) (smooth : PotentialDifferentiable potential)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint)
    (regular : ElectricDifferentiableAt potential (canonicalCauchySlicePoint 0 space)) (data : P286LieBlockData) :
    p286CoordinateLiePairing (p286CoordinateEquiv data)
      (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
        (withMatter potential matter dual) (canonicalCauchySlicePoint 0 space) 3) =
      2*lapse*p286LiePairing data (divergence potential (canonicalCauchySlicePoint 0 space)) +
        (dual (canonicalCauchySlicePoint 0 space) (Stage9DEF.Compatibility.currentAction 0 data
          (matter (canonicalCauchySlicePoint 0 space)))).re := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [Pi.add_apply, p286CoordinateLiePairing_add_right, auxiliary_preserved,
    auxiliary_gauss potential _ regular, charged_projection potential smooth,
    p286CoordinateLiePairing_smul_right]
  simp only [p286CoordinateLiePairing, LinearEquiv.symm_apply_apply]

end
end SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
