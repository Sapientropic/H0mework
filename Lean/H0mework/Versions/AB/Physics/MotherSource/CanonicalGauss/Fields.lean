import H0mework.Versions.AB.Physics.MotherSource.ChargedGauss.Euler
import H0mework.Physics.Cauchy.P286RelativeScalarConstraintOperator
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Source

/-! The original action's normal Legendre writer preserves the actual U scalar momentum on its original initial slice. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option Elab.async false
set_option maxHeartbeats 30000
namespace SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineCanonicalCauchyState StageNineCoframeLocalDifferentiability
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open StageNineScalarActionTemporalMomentumLegendreVelocity StageNineScalarPointwiseEquation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineP286ActionCauchySplit StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open TemporalGauge
open scoped ContDiff
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def configuration (potential : Potential) : StageNineHolonomicConfiguration :=
  p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
    (TemporalGauge.configuration potential)

private theorem scalar_readout (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
      (StageNineFormNativeP286GaugeYangMillsReadout.formNativeP286GaugeConstitutiveReadout source background)
      point direction = holonomicScalarCovariantDerivative background point direction := rfl

private theorem scalar_field_readout (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) :
    (StageNineFormNativeP286GaugeYangMillsReadout.formNativeP286GaugeConstitutiveReadout source background).scalar =
      background.scalar := rfl

private theorem coframe_readout (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) :
    (StageNineFormNativeP286GaugeYangMillsReadout.formNativeP286GaugeConstitutiveReadout source background).coframe =
      background.coframe := rfl

theorem base_scalar (potential : Potential) :
    (TemporalGauge.configuration potential).scalar = Stage10.Runtime.configuration.scalar := by
  rw [TemporalGauge.configuration, Stage10.Runtime.source_eq, scalar_field_readout]
  rfl

theorem base_coframe (potential : Potential) :
    (TemporalGauge.configuration potential).coframe = Stage10.Runtime.configuration.coframe := by
  rw [TemporalGauge.configuration, Stage10.Runtime.source_eq, coframe_readout]
  rfl

theorem base_connection (potential : Potential) :
    (TemporalGauge.configuration potential).gaugeConnection = (primitive potential).gaugeConnection := by
  rw [TemporalGauge.configuration, Stage10.Runtime.source_eq]
  rfl

theorem normal_velocity (potential : Potential) (point : BasePoint) :
    scalarNormalConstraintCovariantVelocity (TemporalGauge.configuration potential) point = 0 := by
  unfold scalarNormalConstraintCovariantVelocity scalarNormalConstraintSpatialDemand
  have spatial (axis : Fin 3) :
      holonomicScalarCovariantDerivative (TemporalGauge.configuration potential) point axis.succ = 0 := by
    rw [TemporalGauge.configuration, Stage10.Runtime.source_eq, scalar_readout]
    rw [scalar_derivative]
    simp
  simp only [spatial, smul_zero, Finset.sum_const_zero]

theorem raw_velocity (potential : Potential) (space : StageNineSpatialPoint) :
    scalarNormalConstraintRawVelocity (TemporalGauge.configuration potential) space =
      -scalarCharge (potential (canonicalCauchySlicePoint 0 space)) := by
  unfold scalarNormalConstraintRawVelocity
  dsimp only
  rw [normal_velocity]
  simp only [base_connection, base_scalar,
    primitive, Stage10.Runtime.configuration_eq, actual_gaugeConnection, actual_scalar,
    canonicalLorentzianTimeDirection, gaugePotential, Matrix.cons_val_zero, ite_true, zero_add,
    zero_sub, scalarCharge, Stage10.Runtime.source_eq]

theorem scalar_field (potential : Potential) (point : BasePoint) :
    (configuration potential).scalar point =
      sourceGeneratedVacuumCoordinates Stage10.Runtime.source +
        canonicalTimeProjection point •
          (-scalarCharge (potential
            (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)))) := by
  unfold configuration p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
  simp only
  rw [Stage10.Runtime.source_eq]
  rw [raw_velocity]
  congr 1
  rw [base_scalar, Stage10.Runtime.configuration_eq, actual_scalar]

theorem noncharacteristic (potential : Potential) (point : BasePoint) :
    coframeTemporalPrincipalScalar ((TemporalGauge.configuration potential).coframe point) ≠ 0 := by
  rw [base_coframe, Stage10.Runtime.configuration_eq]
  exact LowEnergy.FullQuantum.actual_noncharacteristic point

theorem original_momentum (direction : ScalarCoordinateCarrier) (point : BasePoint) :
    scalarTemporalMomentumDualAt Stage10.Runtime.source Stage10.Runtime.configuration point direction = 0 := by
  rw [Stage10.Runtime.source_eq, Stage10.Runtime.configuration_eq]
  exact congrFun (actual_scalarMomentum_zero direction 0) point

def PotentialDifferentiable (potential : Potential) : Prop :=
  Differentiable ℝ (fun point => p286CoordinateEquiv (potential point))

theorem scalar_differentiable (potential : Potential)
    (regular : PotentialDifferentiable potential) :
    Differentiable ℝ (configuration potential).scalar := by
  have slice : Differentiable ℝ (fun point : BasePoint =>
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext space
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
      simp]
    exact canonicalSpatialInclusion.differentiable.comp canonicalSpatialProjection.differentiable
  let chargeMap := (scalarP286ActionBilinear.flip
    (sourceGeneratedVacuumCoordinates Stage10.Runtime.source)).toContinuousLinearMap
  have chargeRegular := chargeMap.differentiable.comp (regular.comp slice)
  have chargeEq : (fun point => chargeMap
      (p286CoordinateEquiv (potential (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))))) =
      fun point => scalarCharge (potential (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))) := by
    funext point
    change scalarMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm
      (p286CoordinateEquiv (potential (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))))))
      (sourceGeneratedVacuumCoordinates Stage10.Runtime.source) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  change Differentiable ℝ (fun point => chargeMap
      (p286CoordinateEquiv (potential (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))))) at chargeRegular
  rw [chargeEq] at chargeRegular
  have fieldEq := funext (scalar_field potential)
  rw [fieldEq]
  exact differentiable_const _ |>.add (canonicalTimeProjection.differentiable.smul chargeRegular.neg)

theorem current_scalar_differentiable (potential : Potential) :
    Differentiable ℝ (TemporalGauge.configuration potential).scalar := by
  rw [base_scalar, Stage10.Runtime.configuration_eq, actual_scalar]
  exact differentiable_const _

theorem momentum_preserved (potential : Potential) (regular : PotentialDifferentiable potential)
    (space : StageNineSpatialPoint) (direction : ScalarCoordinateCarrier) :
    scalarTemporalMomentumDualAt Stage10.Runtime.source (configuration potential)
      (canonicalCauchySlicePoint 0 space) direction =
    scalarTemporalMomentumDualAt Stage10.Runtime.source Stage10.Runtime.configuration
      (canonicalCauchySlicePoint 0 space) direction := by
  rw [original_momentum]
  exact normalConstraint_scalarTemporalMomentum_zeroSlice Stage10.Runtime.source
    (TemporalGauge.configuration potential) space (noncharacteristic potential _)
    (current_scalar_differentiable potential _) (scalar_differentiable potential regular _) direction

theorem covariant_time_zero (potential : Potential) (regular : PotentialDifferentiable potential)
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative (configuration potential)
      (canonicalCauchySlicePoint 0 space) 0 = 0 := by
  have generated := normalConstraint_scalarCovariantDerivative_time_zeroSlice
    (TemporalGauge.configuration potential) space (scalar_differentiable potential regular _)
  rw [normal_velocity] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
