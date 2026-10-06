import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Gauss

/-! The generated Gauss equation is the faithful time restriction of the existing P286 equation. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra
open StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugePointwiseEquation
open Stage9C.Material.SpinPair
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

/-- Full original Lie test inventory of the temporal field equation. -/
def GaussEquation (potential : Potential) (point : BasePoint) : Prop :=
  ∀ data : P286LieBlockData,
    2*lapse * p286LiePairing data (divergence potential point) =
      scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point)) / lapse

theorem gauss_zero_iff (potential : Potential) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) :
    holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
        (configuration potential) point 3 = 0 ↔ GaussEquation potential point := by
  constructor
  · intro zero data
    have result := gauss_projection potential point regular data
    rw [zero] at result
    have pairZero : p286CoordinateLiePairing (p286CoordinateEquiv data) 0 = 0 := by
      simp [p286CoordinateLiePairing, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]
    rw [pairZero] at result
    exact sub_eq_zero.mp result.symm
  · intro equation
    apply (p286CoordinateLiePairing_self_eq_zero_iff _).mp
    let current := holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
      (configuration potential) point 3
    have result := gauss_projection potential point regular (p286CoordinateEquiv.symm current)
    rw [LinearEquiv.apply_symm_apply, equation, sub_self] at result
    exact result

/-- Existing source pointwise acceptance directly entails the computed Gauss equation. -/
theorem original_pointwise_consumer (potential : Potential)
    (equation : FormNativeP286GaugeConnectionPointwiseEquation Stage10.Runtime.source
      (configuration potential)) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) : GaussEquation potential point := by
  have zero := (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_pointwiseEquation
    Stage10.Runtime.source (configuration potential)).mpr equation
  apply (gauss_zero_iff potential point regular).mp
  exact congrFun (congrFun zero point) 3

theorem original_actual (point : BasePoint) : GaussEquation (fun _ => 0) point := by
  have regular : ElectricDifferentiableAt (fun _ => 0) point := by
    intro axis
    simp [electric, derivative, fieldDirectionalDerivative, bracket_zero_left]
  apply (gauss_zero_iff (fun _ => 0) point regular).mp
  rw [configuration_zero, Stage10.Runtime.source_eq, Stage10.Runtime.configuration_eq]
  exact congrFun (actual_gaugeEuler_zero point) 3

end
end SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
