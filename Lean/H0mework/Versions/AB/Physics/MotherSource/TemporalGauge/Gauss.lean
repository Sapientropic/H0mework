import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Charge

/-! The original constitutive gauge equation generates the complete covariant Gauss operator. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
namespace SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineResidualLinearPlebanskiTorsionReduction
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem auxiliary_value (potential : Potential) (point : BasePoint) :
    (configuration potential).gaugeAuxiliary point =
      field (fun axis => -(2*lapse⁻¹) • magnetic axis)
        (fun axis => (2*lapse) • electric potential point axis) := by
  unfold configuration
  rw [Stage10.Runtime.source_eq, formNativeP286GaugeConstitutiveReadout_gaugeAuxiliary, curvature_field]
  have coframe : (primitive potential).coframe point = homogeneousCoframe lapse := by
    simp only [primitive, Stage10.Runtime.configuration_eq, actual_coframe]
  rw [coframe]
  simpa only [Stage10.Runtime.source_eq] using auxiliary (electric potential point) magnetic

theorem auxiliary_coordinates (potential : Potential) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate (configuration potential) point =
      ![-(2*lapse⁻¹) • p286CoordinateEquiv (magnetic 0),
        -(2*lapse⁻¹) • p286CoordinateEquiv (magnetic 1),
        -(2*lapse⁻¹) • p286CoordinateEquiv (magnetic 2),
        (2*lapse) • p286CoordinateEquiv (electric potential point 0),
        (2*lapse) • p286CoordinateEquiv (electric potential point 1),
        (2*lapse) • p286CoordinateEquiv (electric potential point 2)] := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [auxiliary_value]
  funext pair
  fin_cases pair <;> simp [field, map_smul]

def ElectricDifferentiableAt (potential : Potential) (point : BasePoint) : Prop :=
  ∀ axis : Fin 3, DifferentiableAt ℝ
    (fun p => p286CoordinateEquiv (electric potential p axis)) point

theorem auxiliary_differentiable (potential : Potential) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) :
    DifferentiableAt ℝ (holonomicP286GaugeAuxiliaryCoordinate (configuration potential)) point := by
  apply differentiableAt_pi.mpr
  intro pair
  simp only [auxiliary_coordinates]
  fin_cases pair
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · exact (regular 0).fun_const_smul (2*lapse)
  · exact (regular 1).fun_const_smul (2*lapse)
  · exact (regular 2).fun_const_smul (2*lapse)

theorem auxiliary_derivative (potential : Potential) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) (axis : Fin 3) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative (configuration potential) point direction
      (Fin.natAdd 3 axis) =
      (2*lapse) • fieldDirectionalDerivative
        (fun p => p286CoordinateEquiv (electric potential p axis)) point direction := by
  have projection := congrArg (fun L : BasePoint →L[ℝ] P286CoordinateCarrier =>
    L (coordinateDirection direction))
      (fderiv_apply (auxiliary_differentiable potential point regular) (Fin.natAdd 3 axis))
  have component :
      (fun p => holonomicP286GaugeAuxiliaryCoordinate (configuration potential) p (Fin.natAdd 3 axis)) =
      fun p => (2*lapse) • p286CoordinateEquiv (electric potential p axis) := by
    funext p
    fin_cases axis <;> simp [auxiliary_coordinates, Fin.natAdd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at projection
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [← projection, component, fderiv_fun_const_smul (regular axis) (2*lapse)]
  rfl

/-- Divergence of the actual electric curvature, with the original spatial connection. -/
def divergence (potential : Potential) (point : BasePoint) : P286LieBlockData :=
  ∑ axis : Fin 3,
    (derivative (fun p => electric potential p axis) point axis.succ +
      p286LieBracket (gaugeScale • sourceColorP286Generator axis) (electric potential point axis))

theorem spatial_connection (potential : Potential) (point : BasePoint) (axis : Fin 3) :
    holonomicP286GaugeConnectionCoordinate (configuration potential) point axis.succ =
      p286CoordinateEquiv (gaugeScale • sourceColorP286Generator axis) := by
  unfold holonomicP286GaugeConnectionCoordinate configuration
  rw [Stage10.Runtime.source_eq, formNativeP286GaugeConstitutiveReadout_gaugeConnection]
  simp only [primitive, Stage10.Runtime.configuration_eq, actual_gaugeConnection]
  fin_cases axis <;> simp [gaugePotential]

theorem auxiliary_gauss (potential : Potential) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (configuration potential) point 3 =
      (2*lapse) • p286CoordinateEquiv (divergence potential point) := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
  simp only [show threeFormFirst 3 = 1 from rfl, show threeFormSecond 3 = 2 from rfl,
    show threeFormThird 3 = 3 from rfl,
    orderedP286GaugeTwoFormComponent_two_three, orderedP286GaugeTwoFormComponent_three_one,
    orderedP286GaugeTwoFormComponent_one_two,
    pointwiseP286GaugeTwoFormCovariantDerivative, Pi.add_apply, p286GaugeTwoFormAdjoint]
  have d0 := auxiliary_derivative potential point regular 0 1
  have d1 := auxiliary_derivative potential point regular 1 2
  have d2 := auxiliary_derivative potential point regular 2 3
  change p286GaugeAuxiliaryDirectionalDerivative (configuration potential) point 1 3 = _ at d0
  change p286GaugeAuxiliaryDirectionalDerivative (configuration potential) point 2 4 = _ at d1
  change p286GaugeAuxiliaryDirectionalDerivative (configuration potential) point 3 5 = _ at d2
  rw [d0, d1, d2]
  erw [spatial_connection potential point 0, spatial_connection potential point 1,
    spatial_connection potential point 2]
  simp only [auxiliary_coordinates, Matrix.cons_val_three, Matrix.cons_val_four]
  simp [divergence, derivative, fieldDirectionalDerivative,
    p286CoordinateLieBracket, p286LieBracket_smul_right, Fin.sum_univ_three,
    map_add, map_smul, smul_add]

theorem constitutive_charged_preserved (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    formNativeChargedGaugeThreeForm source 0 point
      (toContinuumPointField (formNativeP286GaugeConstitutiveReadout source background) point) =
      formNativeChargedGaugeThreeForm source 0 point (toContinuumPointField background point) := rfl

/-- The time projection of the existing complete Euler three-form, on every original Lie test. -/
theorem gauss_projection (potential : Potential) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) (data : P286LieBlockData) :
    p286CoordinateLiePairing (p286CoordinateEquiv data)
      (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
        (configuration potential) point 3) =
      2*lapse * p286LiePairing data (divergence potential point) -
        scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point)) / lapse := by
  have charged := charged_gauss_projection potential point data
  have auxiliary := auxiliary_gauss potential point regular
  rw [Stage10.Runtime.source_eq] at charged ⊢
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [Pi.add_apply, p286CoordinateLiePairing_add_right, auxiliary]
  have same := constitutive_charged_preserved positiveSmoothUnifiedSource (primitive potential) point
  simp only [configuration, Stage10.Runtime.source_eq] at ⊢
  rw [same, charged, p286CoordinateLiePairing_smul_right]
  simp only [p286CoordinateLiePairing, LinearEquiv.symm_apply_apply]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
