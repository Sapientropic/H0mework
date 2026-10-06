import H0mework.Versions.AB.Physics.MotherSource.StaticHamiltonian.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineFormNativeMotherAction
open StageNineFormNativeGaugeWedge StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing
open StageNineScalarPointwiseEquation StageNineMatterPointwiseEquation StageNineDynamicBreakingVacuum
open StageNineScalarActionTemporalMomentumLegendreVelocity StageNineCanonicalCauchyState
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction SU7MotherLieAlgebra TemporalGauge
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

/-- The d(time) wedge ordinary connection velocity in the original raw curvature convention. -/
def gravityVelocityCurvature (background : StageNineHolonomicConfiguration) (point : BasePoint) : PhysicalBivector :=
  fun internalPair spacetimePair => minkowskiInternalSign (pairFirst internalPair) *
    ((if pairFirst spacetimePair = 0 then gravityConnectionDerivative background point 0
      (pairSecond spacetimePair) (pairFirst internalPair) (pairSecond internalPair) else 0) -
     (if pairSecond spacetimePair = 0 then gravityConnectionDerivative background point 0
      (pairFirst spacetimePair) (pairFirst internalPair) (pairSecond internalPair) else 0))

def gaugeVelocityCurvature (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    Fin 6 → P286LieBlockData :=
  electricForm (fun axis => p286ConnectionDerivative background point 0 axis.succ)

/-- The gauge part of the ordinary-time pairing is the complete mother action's actual primitive time-path derivative. -/
theorem gauge_time_pairing_hasDerivAt (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint)
    (regular : GaugeHamiltonian.ConnectionRegularAt background point) :
    HasDerivAt (fun parameter : ℝ =>
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (StageNineP286GaugeConnectionVariation.varyP286GaugeConnectionCoordinate background
            (GaugeHamiltonian.timeVariation point (fun axis => p286ConnectionDerivative background point 0 axis.succ))
            parameter) point))
      (formNativeP286GaugeWedgeCoefficient (background.gaugeAuxiliary point)
        (gaugeVelocityCurvature background point)) 0 := by
  let velocity : Fin 3 → P286LieBlockData := fun axis => p286ConnectionDerivative background point 0 axis.succ
  have coefficient : StageNineFormNativeP286GaugeConnectionLocalVariation.formNativeP286GaugeConnectionBFFirstVariationDensity
      (toContinuumPointField background point)
      (StageNineFormNativeP286GaugeGeometricKinematics.p286GaugeConnectionExteriorDerivativeVariation
        (GaugeHamiltonian.timeVariation point velocity) point) =
      formNativeP286GaugeWedgeCoefficient (background.gaugeAuxiliary point) (gaugeVelocityCurvature background point) := by
    rw [GaugeHamiltonian.timeVariation_curvature]
    unfold StageNineFormNativeP286GaugeConnectionLocalVariation.formNativeP286GaugeConnectionBFFirstVariationDensity
    congr 1
    funext pair
    fin_cases pair <;> simp [StageNineFormNativeP286GaugeConnectionLocalVariation.formNativeP286GaugeCurvatureCoordinateToActual,
      gaugeVelocityCurvature, electricForm, velocity]
  simp_rw [GaugeHamiltonian.original_action_affine source background point regular]
  convert ((hasDerivAt_id (0 : ℝ)).mul_const
    (StageNineFormNativeP286GaugeConnectionLocalVariation.formNativeP286GaugeConnectionBFFirstVariationDensity
      (toContinuumPointField background point)
      (StageNineFormNativeP286GaugeGeometricKinematics.p286GaugeConnectionExteriorDerivativeVariation
        (GaugeHamiltonian.timeVariation point velocity) point))).const_add
      (sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point (toContinuumPointField background point)) using 1 <;> try rfl
  simpa only [one_mul] using coefficient.symm

/-- All derivative-bearing blocks of the complete mother action. Coframe, auxiliaries, multipliers and independent dual have algebraic slots in this action. -/
def ordinaryTimePairing (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (point : BasePoint) : ℝ :=
  gravityTopologicalBFCoefficient (background.gravityAuxiliary point) (gravityVelocityCurvature background point) +
  formNativeP286GaugeWedgeCoefficient (background.gaugeAuxiliary point) (gaugeVelocityCurvature background point) +
  scalarDifferentialMomentum source background (fieldDirectionalDerivative background.scalar point 0) 0 point +
  matterDifferentialMomentum source background
    (fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv (background.matter candidate)) point 0) 0 point

def hamiltonianDensity (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (point : BasePoint) : ℝ :=
  ordinaryTimePairing source background point -
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point (toContinuumPointField background point)

private theorem gauge_velocity_zero_of_spatial_constant (background : StageNineHolonomicConfiguration)
    (spatial : Fin 3 → P286LieBlockData) (constant : ∀ axis, (fun point => background.gaugeConnection point axis.succ) = fun _ => spatial axis)
    (point : BasePoint) : gaugeVelocityCurvature background point = 0 := by
  have derivative (axis : Fin 3) : p286ConnectionDerivative background point 0 axis.succ = 0 := by
    unfold p286ConnectionDerivative
    have same : (fun candidate => p286CoordinateEquiv (background.gaugeConnection candidate axis.succ)) =
        fun _ : BasePoint => p286CoordinateEquiv (spatial axis) :=
      funext fun candidate => congrArg p286CoordinateEquiv (congrFun (constant axis) candidate)
    rw [same]
    simp [fieldDirectionalDerivative]
  have same : (fun axis : Fin 3 => p286ConnectionDerivative background point 0 axis.succ) = 0 := funext derivative
  unfold gaugeVelocityCurvature
  rw [same]
  simp [electricForm]

private theorem gravity_velocity_zero_of_constant (background : StageNineHolonomicConfiguration)
    (connection : PointwiseLorentzSpinConnection) (constant : background.gravityConnection = fun _ => connection)
    (point : BasePoint) : gravityVelocityCurvature background point = 0 := by
  funext internalPair spacetimePair
  simp [gravityVelocityCurvature, gravityConnectionDerivative, constant]

private theorem connection_normal (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier) (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :
    (ChargedGauss.replaceMatter (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background)
      matter dual).gaugeConnection = background.gaugeConnection := rfl

private theorem gravity_normal (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier) (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :
    (ChargedGauss.replaceMatter (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background)
      matter dual).gravityConnection = background.gravityConnection := rfl

private theorem gauge_reference_velocity (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    gaugeVelocityCurvature (reference matter dual) point = 0 := by
  apply gauge_velocity_zero_of_spatial_constant _ (fun axis => gaugeScale • sourceColorP286Generator axis)
  intro axis
  funext point
  change Stage10.Runtime.configuration.gaugeConnection point axis.succ = _
  rw [Stage10.Runtime.configuration_eq, actual_gaugeConnection]
  fin_cases axis <;> rfl

private theorem gauge_canonical_velocity (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    gaugeVelocityCurvature (CanonicalGauss.withMatter potential matter dual) point = 0 := by
  apply gauge_velocity_zero_of_spatial_constant _ (fun axis => gaugeScale • sourceColorP286Generator axis)
  intro axis
  funext point
  unfold CanonicalGauss.withMatter CanonicalGauss.configuration
  rw [connection_normal, CanonicalGauss.base_connection]
  simp only [primitive, Stage10.Runtime.configuration_eq, actual_gaugeConnection, Fin.succ_ne_zero,
    if_false, add_zero]
  fin_cases axis <;> rfl

private theorem scalar_momentum_replace (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier) (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : ScalarCoordinateCarrier) (point : BasePoint) :
    scalarDifferentialMomentum source (ChargedGauss.replaceMatter background matter dual) direction 0 point =
      scalarDifferentialMomentum source background direction 0 point := rfl

private theorem matter_momentum_preserved (source : SmoothUnifiedSource) (potential : Potential)
    (matter : BasePoint → DiracExteriorMatterCarrier) (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : MatterCoordinateCarrier) (point : BasePoint) :
    matterDifferentialMomentum source (CanonicalGauss.withMatter potential matter dual) direction 0 point =
      matterDifferentialMomentum source (reference matter dual) direction 0 point := by
  unfold matterDifferentialMomentum matterDifferentialVariationVector
  simp only [toContinuumPointField, CanonicalGauss.withMatter, ChargedGauss.replaceMatter,
    reference, CanonicalGauss.configuration, generatedVolumeDensity]
  rfl

theorem ordinary_time_pairing_preserved (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential)
    (matter : BasePoint → DiracExteriorMatterCarrier) (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (space : StageNineSpatialPoint) :
    ordinaryTimePairing Stage10.Runtime.source (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space) =
      ordinaryTimePairing Stage10.Runtime.source (reference matter dual) (canonicalCauchySlicePoint 0 space) := by
  have referenceGravity : (reference matter dual).gravityConnection = fun _ => homogeneousConnection spinScale := by
    change Stage10.Runtime.configuration.gravityConnection = _
    rw [Stage10.Runtime.configuration_eq, actual_gravityConnection]
  have canonicalGravity : (CanonicalGauss.withMatter potential matter dual).gravityConnection = fun _ => homogeneousConnection spinScale := by
    unfold CanonicalGauss.withMatter CanonicalGauss.configuration
    rw [gravity_normal]
    change Stage10.Runtime.configuration.gravityConnection = _
    rw [Stage10.Runtime.configuration_eq, actual_gravityConnection]
  have scalarCanonical (direction : ScalarCoordinateCarrier) :
      scalarDifferentialMomentum Stage10.Runtime.source (CanonicalGauss.withMatter potential matter dual) direction 0 (canonicalCauchySlicePoint 0 space) = 0 := by
    unfold CanonicalGauss.withMatter
    rw [Stage10.Runtime.source_eq, scalar_momentum_replace]
    have original := CanonicalGauss.momentum_preserved potential regular space direction
    rw [CanonicalGauss.original_momentum, Stage10.Runtime.source_eq] at original
    exact original
  have scalarReference (direction : ScalarCoordinateCarrier) :
      scalarDifferentialMomentum Stage10.Runtime.source (reference matter dual) direction 0 (canonicalCauchySlicePoint 0 space) = 0 := by
    rw [Stage10.Runtime.source_eq, reference, scalar_momentum_replace]
    have original := CanonicalGauss.original_momentum direction (canonicalCauchySlicePoint 0 space)
    rw [Stage10.Runtime.source_eq] at original
    exact original
  unfold ordinaryTimePairing
  rw [gravity_velocity_zero_of_constant _ _ canonicalGravity,
    gravity_velocity_zero_of_constant _ _ referenceGravity, gauge_canonical_velocity, gauge_reference_velocity,
    scalarCanonical, scalarReference]
  have zeroGravity (value : PhysicalBivector) : gravityTopologicalBFCoefficient value 0 = 0 := by
    simp [gravityTopologicalBFCoefficient]
  simp only [zeroGravity, formNativeP286GaugeWedgeCoefficient_zero_right, zero_add, add_zero]
  rw [Stage10.Runtime.source_eq, matter_momentum_preserved]
  rfl

theorem original_hamiltonian_shift (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential)
    (matter : BasePoint → DiracExteriorMatterCarrier) (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (space : StageNineSpatialPoint) :
    hamiltonianDensity Stage10.Runtime.source (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space) -
      hamiltonianDensity Stage10.Runtime.source (reference matter dual) (canonicalCauchySlicePoint 0 space) =
      -lapse*squared (electric potential (canonicalCauchySlicePoint 0 space)) -
      (dual (canonicalCauchySlicePoint 0 space) (Stage9DEF.Compatibility.currentAction 0
        (potential (canonicalCauchySlicePoint 0 space)) (matter (canonicalCauchySlicePoint 0 space)))).re := by
  unfold hamiltonianDensity
  rw [ordinary_time_pairing_preserved potential regular, complete_static_density potential regular]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
