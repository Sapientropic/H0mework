import H0mework.Versions.AB.Physics.MotherSource.ChargedGauss.Fields

/-! Exact prepared-matter forcing in the original complete Gauss Euler component. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedGauss
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open Stage9C.Material.SpinPair DiracExteriorMatterAction
open TemporalGauge
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

theorem charged_projection (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    p286CoordinateLiePairing (p286CoordinateEquiv data)
      (formNativeChargedGaugeThreeForm Stage10.Runtime.source 0 point
        (toContinuumPointField (withMatter potential matter dual) point) 3) =
      -scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point))/lapse +
        (dual point (Stage9DEF.Compatibility.currentAction 0 data (matter point))).re := by
  have result := formNativeChargedGaugeThreeForm_evaluation Stage10.Runtime.source 0 point
    (toContinuumPointField (withMatter potential matter dual) point) (temporalTest data)
  rw [charged_coefficient] at result
  have zeroPair (value : P286CoordinateCarrier) : p286CoordinateLiePairing 0 value = 0 := by
    simp [p286CoordinateLiePairing, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]
  simpa [p286GaugeOneFormThreeFormWedgeCoefficient, temporalTest,
    Fin.sum_univ_four, oneWedgeThreeSign, missingTripleOfOneForm, zeroPair] using result

theorem auxiliary_preserved (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (withMatter potential matter dual) point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (TemporalGauge.configuration potential) point := rfl

theorem gauss_projection (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) (data : P286LieBlockData) :
    p286CoordinateLiePairing (p286CoordinateEquiv data)
      (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
        (withMatter potential matter dual) point 3) =
      2*lapse*p286LiePairing data (divergence potential point) -
        scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point))/lapse +
        (dual point (Stage9DEF.Compatibility.currentAction 0 data (matter point))).re := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [Pi.add_apply, p286CoordinateLiePairing_add_right, auxiliary_preserved,
    auxiliary_gauss potential point regular, charged_projection, p286CoordinateLiePairing_smul_right]
  simp only [p286CoordinateLiePairing, LinearEquiv.symm_apply_apply]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedGauss
