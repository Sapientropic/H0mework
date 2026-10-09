import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedStaticSpatialRead
import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Poisson

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticVoltageSource
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineCanonicalCauchyState StageNineCoframeLocalDifferentiability
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation Stage9C.Material.SpinPair
open Stage10 Stage10.TemporalGauge
open scoped BigOperators Topology
attribute [local irreducible] Runtime.configuration Runtime.source

/-- This is the original scalar-normal Cauchy family, with its constitutive gauge auxiliary field. -/
def sourceVoltageConfiguration (profile : BasePoint→ℝ) (amplitude : ℝ) : StageNineHolonomicConfiguration :=
  CanonicalGauss.configuration (CanonicalGauss.abelianPotential (fun x=>amplitude*profile x))

theorem sourceVoltage_base (profile : BasePoint→ℝ) : sourceVoltageConfiguration profile 0=Runtime.configuration := by
  have same : CanonicalGauss.configuration (fun _=>0)=TemporalGauge.configuration (fun _=>0) := by
    apply StageNineHolonomicConfiguration.ext
    · exact normalConstraint_coframe _
    · exact normalConstraint_gravityConnection _
    · exact normalConstraint_gravityAuxiliary _
    · exact normalConstraint_gravitySimplicityMultiplier _
    · exact normalConstraint_gaugeConnection _
    · exact normalConstraint_gaugeAuxiliary _
    · funext point
      rw [CanonicalGauss.scalar_field,CanonicalGauss.base_scalar,Runtime.configuration_eq,actual_scalar]
      rw [scalarCharge,Runtime.source_eq]
      simp [p286LieBlockEmbed_zero,scalarMotherLieAction]
    · exact normalConstraint_matter _
    · exact normalConstraint_conjugateMatter _
  have potential : CanonicalGauss.abelianPotential (fun x=>0*profile x)=(fun _=>0) := by
    funext point
    change (0*profile point) • HyperchargeResponse.chargeDirection=0
    rw [zero_mul,zero_smul]
  change CanonicalGauss.configuration (CanonicalGauss.abelianPotential (fun x=>0*profile x))=Runtime.configuration
  rw [potential]
  exact same.trans TemporalGauge.configuration_zero

private theorem scalarCharge_smul (a : ℝ) (v : P286LieBlockData) : scalarCharge (a • v)=a • scalarCharge v := by
  unfold scalarCharge
  rw [p286LieBlockEmbed_real_smul,scalarMotherLieAction_real_smul]

def sourceVoltageScalarTangent (profile : BasePoint→ℝ) (point : BasePoint) : ScalarCoordinateCarrier :=
  -(canonicalTimeProjection point*profile (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))) •
    scalarCharge HyperchargeResponse.chargeDirection

/-- The time-dependent scalar tangent is produced by the actual normal constraint, not appended to the Fourier field. -/
theorem sourceVoltage_scalar (profile : BasePoint→ℝ) (amplitude : ℝ) (point : BasePoint) :
    (sourceVoltageConfiguration profile amplitude).scalar point=
      Runtime.configuration.scalar point+amplitude • sourceVoltageScalarTangent profile point := by
  rw [sourceVoltageConfiguration,CanonicalGauss.scalar_field]
  simp only [CanonicalGauss.abelianPotential,scalarCharge_smul]
  rw [Runtime.configuration_eq,actual_scalar]
  rw [Runtime.source_eq]
  unfold sourceVoltageScalarTangent
  module

theorem sourceVoltage_scalar_hasDerivAt (profile : BasePoint→ℝ) (amplitude : ℝ) (point : BasePoint)
    (index : ScalarBasisIndex) :
    HasDerivAt (fun a=>(sourceVoltageConfiguration profile a).scalar point index)
      (sourceVoltageScalarTangent profile point index) amplitude := by
  simp_rw [sourceVoltage_scalar]
  change HasDerivAt (fun a=>Runtime.configuration.scalar point index+a • sourceVoltageScalarTangent profile point index) _ _
  convert (hasDerivAt_const amplitude (Runtime.configuration.scalar point index)).add
    ((hasDerivAt_id amplitude).smul_const (sourceVoltageScalarTangent profile point index)) using 1 <;> first | rfl | simp

theorem sourceVoltage_scalar_slice (profile : BasePoint→ℝ) (amplitude : ℝ) (space : StageNineSpatialPoint) :
    (sourceVoltageConfiguration profile amplitude).scalar (canonicalCauchySlicePoint 0 space)=
      Runtime.configuration.scalar (canonicalCauchySlicePoint 0 space) := by
  rw [sourceVoltage_scalar]
  simp [sourceVoltageScalarTangent]

theorem sourceVoltage_connection (profile : BasePoint→ℝ) (amplitude : ℝ) (point : BasePoint) (mu : LorentzianIndex) :
    (sourceVoltageConfiguration profile amplitude).gaugeConnection point mu=
      Runtime.configuration.gaugeConnection point mu+
        if mu=0 then (amplitude*profile point) • HyperchargeResponse.chargeDirection else 0 := by
  rfl

theorem sourceVoltage_coframe (profile : BasePoint→ℝ) (amplitude : ℝ) :
    (sourceVoltageConfiguration profile amplitude).coframe=Runtime.configuration.coframe := rfl

theorem sourceVoltage_matter (profile : BasePoint→ℝ) (amplitude : ℝ) :
    (sourceVoltageConfiguration profile amplitude).matter=Runtime.configuration.matter ∧
    (sourceVoltageConfiguration profile amplitude).conjugateMatter=Runtime.configuration.conjugateMatter := ⟨rfl,rfl⟩

/-- The original gauge-B constitutive law is retained in the voltage family. -/
theorem sourceVoltage_auxiliary (profile : BasePoint→ℝ) (amplitude : ℝ) (point : BasePoint) :
    (sourceVoltageConfiguration profile amplitude).gaugeAuxiliary point=
      TemporalGauge.field (fun axis=>-(2*lapse⁻¹) • TemporalGauge.magnetic axis)
        (fun axis=>(2*lapse) • TemporalGauge.electric
          (CanonicalGauss.abelianPotential (fun x=>amplitude*profile x)) point axis) := by
  change (TemporalGauge.configuration (CanonicalGauss.abelianPotential (fun x=>amplitude*profile x))).gaugeAuxiliary point=_
  exact TemporalGauge.auxiliary_value _ _

theorem sourceVoltage_scalar_temporal (profile : BasePoint→ℝ) (space : StageNineSpatialPoint) :
    scalarNormalConstraintRawVelocity (TemporalGauge.configuration (CanonicalGauss.abelianPotential profile)) space=
      -(profile (canonicalCauchySlicePoint 0 space)) • scalarCharge HyperchargeResponse.chargeDirection := by
  rw [CanonicalGauss.raw_velocity]
  simp only [CanonicalGauss.abelianPotential,scalarCharge_smul,neg_smul]

private theorem profile_derivative (profile : BasePoint→ℝ) (regular : Differentiable ℝ profile)
    (a : ℝ) (point : BasePoint) (axis : LorentzianIndex) :
    fieldDirectionalDerivative (fun x=>a*profile x) point axis=a*fieldDirectionalDerivative profile point axis := by
  have derivative : HasFDerivAt (fun x=>a*profile x) (a • fderiv ℝ profile point) point :=
    (regular point).hasFDerivAt.const_smul a
  simp only [fieldDirectionalDerivative,derivative.fderiv,smul_apply,smul_eq_mul]

theorem sourceVoltage_electric (profile : BasePoint→ℝ) (regular : Differentiable ℝ profile)
    (amplitude : ℝ) (point : BasePoint) (axis : Fin 3) :
    TemporalGauge.electric (CanonicalGauss.abelianPotential (fun x=>amplitude*profile x)) point axis=
      amplitude • (-(fieldDirectionalDerivative profile point axis.succ) • HyperchargeResponse.chargeDirection) := by
  rw [CanonicalGauss.electric_abelian _ _ ((regular point).const_mul amplitude),profile_derivative profile regular]
  module

def sourceVoltageAuxiliaryTangent (profile : BasePoint→ℝ) (point : BasePoint) : Fin 6→P286LieBlockData :=
  TemporalGauge.field (fun _=>0)
    (fun axis=> (-(2*lapse)*fieldDirectionalDerivative profile point axis.succ) • HyperchargeResponse.chargeDirection)

/-- Gauge-B is the same constitutive response; it is not frozen while the voltage varies. -/
theorem sourceVoltage_auxiliary_affine (profile : BasePoint→ℝ) (regular : Differentiable ℝ profile)
    (amplitude : ℝ) (point : BasePoint) :
    (sourceVoltageConfiguration profile amplitude).gaugeAuxiliary point=
      Runtime.configuration.gaugeAuxiliary point+amplitude • sourceVoltageAuxiliaryTangent profile point := by
  have base := sourceVoltage_auxiliary profile 0 point
  rw [sourceVoltage_base] at base
  rw [sourceVoltage_auxiliary,base]
  simp only [sourceVoltage_electric profile regular,zero_smul,smul_zero]
  funext pair
  fin_cases pair <;> simp [TemporalGauge.field,sourceVoltageAuxiliaryTangent,smul_smul,
    mul_assoc,mul_left_comm,mul_comm]

end LowEnergy.PreparationVacuumStaticVoltageSource
