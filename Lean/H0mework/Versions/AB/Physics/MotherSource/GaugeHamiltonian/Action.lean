import H0mework.Versions.AB.Physics.MotherSource.GaugeHamiltonian.Momentum

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.GaugeHamiltonian
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineFormNativeP286GaugeConnectionLocalVariation StageNineTopologicalFourFormPairing
open StageNineFormNativeP286GaugeGeometricKinematics StageNineFormNativeGaugeWedge
open StageNineDiracDualFormNativeMotherAction StageNineFormNativeMotherAction
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open Stage9C.Material.SpinPair TemporalGauge
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def ConnectionRegularAt (background : StageNineHolonomicConfiguration) (point : BasePoint) : Prop :=
  ∀ direction, DifferentiableAt ℝ
    (fun candidate => holonomicP286GaugeConnectionCoordinate background candidate direction) point

private theorem coordinate_derivative (background : StageNineHolonomicConfiguration)
    (point : BasePoint) (regular : ConnectionRegularAt background point)
    (velocity : Fin 3 → P286LieBlockData) (parameter : ℝ) (d f : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
      (varyP286GaugeConnectionCoordinate background (timeVariation point velocity) parameter) point d f =
    p286GaugeConnectionCoordinateDerivative background point d f +
      parameter • p286GaugeVariationCoordinateDerivative (timeVariation point velocity) point d f := by
  have variationRegular : DifferentiableAt ℝ
      (fun candidate => timeVariation point velocity candidate f) point := by
    change DifferentiableAt ℝ (fun candidate : BasePoint =>
      (candidate 0-point 0) • spatialVariation velocity f) point
    exact (((EuclideanSpace.proj 0 : BasePoint →L[ℝ] ℝ).differentiableAt).sub_const _).smul_const _
  unfold p286GaugeConnectionCoordinateDerivative p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  simp only [holonomicP286GaugeConnectionCoordinate_vary, Pi.add_apply, Pi.smul_apply]
  have derivative : fderiv ℝ
      (fun candidate => holonomicP286GaugeConnectionCoordinate background candidate f +
        parameter • timeVariation point velocity candidate f) point =
      fderiv ℝ (fun candidate => holonomicP286GaugeConnectionCoordinate background candidate f) point +
        parameter • fderiv ℝ (fun candidate => timeVariation point velocity candidate f) point :=
    ((regular f).hasFDerivAt.add (variationRegular.hasFDerivAt.const_smul parameter)).fderiv
  rw [derivative]
  rfl

theorem point_field (background : StageNineHolonomicConfiguration) (point : BasePoint)
    (regular : ConnectionRegularAt background point)
    (velocity : Fin 3 → P286LieBlockData) (parameter : ℝ) :
    toContinuumPointField
      (varyP286GaugeConnectionCoordinate background (timeVariation point velocity) parameter) point =
    withP286GaugeConnectionJets (toContinuumPointField background point)
      (p286CurvatureCoordinate (toContinuumPointField background point) +
        parameter • p286GaugeConnectionExteriorDerivativeVariation (timeVariation point velocity) point)
      (toContinuumPointField background point).scalarCovariantDerivative
      (toContinuumPointField background point).matterCovariantDerivative := by
  refine StageNineContinuumPointField.ext rfl rfl rfl rfl ?_ rfl rfl ?_ rfl ?_ rfl
  · funext pair
    apply p286CoordinateEquiv.injective
    change holonomicP286GaugeCurvatureCoordinate
      (varyP286GaugeConnectionCoordinate background (timeVariation point velocity) parameter) point pair =
        p286CoordinateEquiv (p286CoordinateEquiv.symm _)
    rw [p286CoordinateEquiv.apply_symm_apply]
    change _ = holonomicP286GaugeCurvatureCoordinate background point pair + parameter • _
    rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket,
      coordinate_derivative background point regular,
      coordinate_derivative background point regular,
      holonomicP286GaugeConnectionCoordinate_vary, timeVariation_zero]
    simp only [smul_zero, add_zero]
    rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
    unfold p286GaugeConnectionExteriorDerivativeVariation
    module
  · funext direction
    change holonomicScalarCovariantDerivative _ point direction = holonomicScalarCovariantDerivative _ point direction
    rw [holonomicScalarCovariantDerivative_gaugeConnection_expansion,
      holonomicScalarGaugeConnectionVariation_eq_zero _ _ _ (timeVariation_zero point velocity)]
    simp
  · funext direction
    change holonomicMatterCovariantDerivative _ point direction = holonomicMatterCovariantDerivative _ point direction
    rw [holonomicMatterCovariantDerivative_gaugeConnection_expansion,
      holonomicMatterGaugeConnectionVariation_eq_zero _ _ _ (timeVariation_zero point velocity)]
    change _ + (parameter : ℂ) • (0 : DiracExteriorMatterAction.DiracExteriorMatterCarrier) = _
    rw [smul_zero, add_zero]

private theorem density_affine (source : SmoothUnifiedSource) (field : StageNineContinuumPointField)
    (point : BasePoint) (variation : P286GaugeTwoForm) (parameter : ℝ) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field + parameter • variation)
        field.scalarCovariantDerivative field.matterCovariantDerivative) =
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point field +
      parameter * formNativeP286GaugeConnectionBFFirstVariationDensity field variation := by
  have gauge := generatedFormNativeGaugeDensityAtBoundary_connectionJets_quadratic
    (sourceGeneratedUnifiedCouplings source) field variation 0
    field.scalarCovariantDerivative field.matterCovariantDerivative parameter
  have zero : formNativeP286GaugeConnectionBFFirstVariationDensity field 0 = 0 := by
    simp [formNativeP286GaugeConnectionBFFirstVariationDensity]
  simp only [smul_zero, add_zero, zero, mul_zero] at gauge
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [gauge]
  have gravity : generatedFormNativeGravityBFDensity
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field + parameter • variation)
        field.scalarCovariantDerivative field.matterCovariantDerivative) =
      generatedFormNativeGravityBFDensity field := rfl
  have constraint : generatedFormNativeGravityConstraintDensity
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field + parameter • variation)
        field.scalarCovariantDerivative field.matterCovariantDerivative) =
      generatedFormNativeGravityConstraintDensity field := rfl
  have matter : generatedDiracDualFormNativeMatterDensity source 0 point
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field + parameter • variation)
        field.scalarCovariantDerivative field.matterCovariantDerivative) =
      generatedDiracDualFormNativeMatterDensity source 0 point field := rfl
  rw [gravity, constraint, matter]
  ring

theorem original_action_affine (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint)
    (regular : ConnectionRegularAt background point) (velocity : Fin 3 → P286LieBlockData) (parameter : ℝ) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
      (toContinuumPointField (varyP286GaugeConnectionCoordinate background
        (timeVariation point velocity) parameter) point) =
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
      (toContinuumPointField background point) + parameter *
    formNativeP286GaugeConnectionBFFirstVariationDensity (toContinuumPointField background point)
      (p286GaugeConnectionExteriorDerivativeVariation (timeVariation point velocity) point) := by
  rw [point_field background point regular, density_affine]

private theorem normal_connection (background : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background).gaugeConnection =
      background.gaugeConnection := rfl

theorem canonical_connection_regular (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential) (point : BasePoint) :
    ConnectionRegularAt (CanonicalGauss.configuration potential) point := by
  intro direction
  unfold holonomicP286GaugeConnectionCoordinate
  rw [CanonicalGauss.configuration, normal_connection, CanonicalGauss.base_connection]
  simp only [primitive, Stage10.Runtime.configuration_eq, actual_gaugeConnection, map_add]
  by_cases zero : direction = 0
  · simp only [zero, if_pos, gaugePotential, Matrix.cons_val_zero, map_zero, zero_add]
    exact regular point
  · simp only [zero, if_false, map_zero, add_zero]
    exact differentiableAt_const _

theorem source_action_affine (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential) (point : BasePoint)
    (velocity : Fin 3 → P286LieBlockData) (parameter : ℝ) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (varyP286GaugeConnectionCoordinate (CanonicalGauss.configuration potential)
        (timeVariation point velocity) parameter) point) =
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (CanonicalGauss.configuration potential) point) +
      parameter * momentum potential point velocity := by
  rw [Stage10.Runtime.source_eq]
  exact original_action_affine _ _ point (canonical_connection_regular potential regular point) velocity parameter

theorem source_action_hasDerivAt (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential) (point : BasePoint)
    (velocity : Fin 3 → P286LieBlockData) :
    HasDerivAt (fun parameter : ℝ =>
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
        (toContinuumPointField (varyP286GaugeConnectionCoordinate (CanonicalGauss.configuration potential)
          (timeVariation point velocity) parameter) point))
      (2*lapse*∑ i : Fin 3, formNativeP286LiePairing (electric potential point i) (velocity i)) 0 := by
  simp_rw [source_action_affine potential regular point velocity]
  convert ((hasDerivAt_id (0 : ℝ)).mul_const (momentum potential point velocity)).const_add
    (sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (CanonicalGauss.configuration potential) point)) using 1 <;> try rfl
  simpa only [one_mul] using (momentum_readout potential point velocity).symm

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeHamiltonian
