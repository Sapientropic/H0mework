import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Gauge

/-! The complete scalar and independent-dual response to a Lie-valued temporal potential. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualYukawaLocalSpinDensity
open StageNineP286GaugeConnectionActionVariation StageNineScalarLocalSpinDensity
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift StageNineCoframeSpinRepresentation
open StageNineMatterVariation StageNineCoframeLocalDifferentiability
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def scalarCharge (data : P286LieBlockData) : ScalarCoordinateCarrier :=
  scalarMotherLieAction (p286LieBlockEmbed data)
    (sourceGeneratedVacuumCoordinates Stage10.Runtime.source)

theorem scalar_derivative (potential : Potential) (point : BasePoint) (d : LorentzianIndex) :
    holonomicScalarCovariantDerivative (primitive potential) point d =
      if d = 0 then scalarCharge (potential point) else 0 := by
  have original := congrFun (actual_scalarCovariantDerivative_zero point) d
  have originalAction :
      scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point d))
        (actual.scalar point) = 0 := by
    simpa [holonomicScalarCovariantDerivative, actual_scalar, fieldDirectionalDerivative] using original
  simp only [holonomicScalarCovariantDerivative, primitive, Stage10.Runtime.configuration_eq,
    p286LieBlockEmbed_add, scalarMotherLieAction_add, originalAction, zero_add]
  rw [actual_scalar]
  rw [scalarCharge, Stage10.Runtime.source_eq]
  split_ifs <;> simp [fieldDirectionalDerivative, p286LieBlockEmbed_zero, scalarMotherLieAction]

theorem scalar_kinetic (potential : Potential) (point : BasePoint) :
    generatedScalarKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      -scalarCoordinateSquaredNorm (scalarCharge (potential point)) / (2*lapse^2) := by
  have derivative : holonomicScalarCovariantDerivative (primitive potential) point =
      fun direction => if direction = 0 then scalarCharge (potential point) else 0 :=
    funext (scalar_derivative potential point)
  unfold generatedScalarKineticDensity
  simp only [toContinuumPointField]
  rw [derivative]
  simp only [scalarFrameRelativeCovariantDerivative, Stage10.Runtime.source_eq,
    scalarFrameRelativeCoordinates_zeroChart]
  have coframe : (primitive potential).coframe point = actual.coframe point := by
    simp only [primitive, Stage10.Runtime.configuration_eq]
  rw [coframe]
  exact LowEnergy.Response.ScalarSignature.temporal_kinetic point (scalarCharge (potential point))

def matterCharge (data : P286LieBlockData) (point : BasePoint) : DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed data)
    (Stage10.Runtime.configuration.matter point)

theorem matter_derivative (potential : Potential) (point : BasePoint) (d : LorentzianIndex) :
    holonomicMatterCovariantDerivative (primitive potential) point d =
      holonomicMatterCovariantDerivative Stage10.Runtime.configuration point d +
        if d = 0 then matterCharge (potential point) point else 0 := by
  simp only [holonomicMatterCovariantDerivative, primitive, p286LieBlockEmbed_add,
    diracExteriorMotherLieAction_add, LinearMap.add_apply, matterCharge]
  split_ifs
  · module
  · simp [p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix]

theorem temporal_dual_zero (data : P286LieBlockData) (point : BasePoint) :
    Stage10.Runtime.configuration.conjugateMatter point
      (Complex.I • diracMatrixMatterAction (diracGamma 0) (matterCharge data point)) = 0 := by
  rw [matterCharge, Stage10.Runtime.configuration_eq]
  have result := Stage9DEF.Compatibility.current_classical_quantum point 0 data
  rw [actual_spinPairCurrent_time] at result
  exact (Stage9DEF.Compatibility.actual_action_quantumResponse point
    (Stage9DEF.Compatibility.currentAction 0 data)).trans result.symm

theorem kinetic_operator_preserved (source : SmoothUnifiedSource)
    (potential : Potential) (point : BasePoint)
    (derivative : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterCovariantDerivativeVariationVector source 0 point
      (toContinuumPointField (primitive potential) point) derivative =
    matterCovariantDerivativeVariationVector source 0 point
      (toContinuumPointField Stage10.Runtime.configuration point) derivative := by
  simp only [matterCovariantDerivativeVariationVector, matterCovariantDerivativeKineticSum,
    toContinuumPointField, primitive]

theorem kinetic_increment (potential : Potential) (point : BasePoint) :
    generatedContinuumMatterKineticVector Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedContinuumMatterKineticVector Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) +
      ((lapse⁻¹ : ℝ) : ℂ) •
        (Complex.I • diracMatrixMatterAction (diracGamma 0) (matterCharge (potential point) point)) := by
  have derivative : holonomicMatterCovariantDerivative (primitive potential) point =
      holonomicMatterCovariantDerivative Stage10.Runtime.configuration point +
        (fun direction => if direction = 0 then matterCharge (potential point) point else 0) :=
    funext (matter_derivative potential point)
  rw [Stage10.Runtime.source_eq]
  unfold generatedContinuumMatterKineticVector
  change matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point
    (toContinuumPointField (primitive potential) point)
    (holonomicMatterCovariantDerivative (primitive potential) point) = _
  rw [kinetic_operator_preserved, derivative, matterCovariantDerivativeVariationVector_add]
  apply congrArg (fun vector =>
    matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField Stage10.Runtime.configuration point)
      (holonomicMatterCovariantDerivative Stage10.Runtime.configuration point) + vector)
  unfold matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField,
    Stage10.Runtime.configuration_eq, actual_coframe]
  simp [Fin.sum_univ_four, homogeneousInverseGamma lapse (ne_of_gt lapse_pos),
    coframeDiracMatrixMatterAction_smul_matrix, smul_smul, mul_comm]

theorem dirac_density_preserved (potential : Potential) (point : BasePoint) :
    generatedDensitizedContinuumDiracDualMatterDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedDensitizedContinuumDiracDualMatterDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) := by
  have increment := kinetic_increment potential point
  rw [Stage10.Runtime.source_eq] at increment ⊢
  unfold generatedDensitizedContinuumDiracDualMatterDensity
  have yukawa : generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) := by
    simp only [generatedDensitizedContinuumDiracDualYukawaDensity,
      generatedContinuumDiracDualYukawaVector, generatedVolumeDensity, toContinuumPointField, primitive]
  rw [yukawa]
  apply congrArg (fun value => value +
    generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField Stage10.Runtime.configuration point))
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [increment]
  simp only [generatedVolumeDensity, toContinuumPointField, primitive, matterDualFrameRelative_chartZero]
  rw [map_add, map_smul, temporal_dual_zero, smul_zero, add_zero]

theorem scalar_density_shift (potential : Potential) (point : BasePoint) :
    generatedDensitizedContinuumScalarDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedDensitizedContinuumScalarDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) -
      scalarCoordinateSquaredNorm (scalarCharge (potential point)) / (2*lapse) := by
  have kinetic := scalar_kinetic potential point
  rw [Stage10.Runtime.source_eq] at kinetic ⊢
  have original : generatedScalarKineticDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField Stage10.Runtime.configuration point) = 0 := by
    rw [Stage10.Runtime.configuration_eq]
    simp [generatedScalarKineticDensity, toContinuumPointField,
      actual_scalarCovariantDerivative_zero, scalarFrameRelativeCovariantDerivative,
      scalarCoordinatePairingRe]
  unfold generatedDensitizedContinuumScalarDensity
  rw [kinetic, original]
  simp only [generatedVolumeDensity, toContinuumPointField, primitive]
  rw [Stage10.Runtime.configuration_eq, actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  field_simp [ne_of_gt lapse_pos]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
