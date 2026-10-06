import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Consumer
import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Classical

/-! The original Gauss equation reads actual prepared matter and independent-dual fields. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedGauss
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality StageNineFormNativeP286GaugeGeometricFirstVariation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineCoframeLocalDifferentiability StageNineMatterVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open TemporalGauge
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def replaceMatter (background : StageNineHolonomicConfiguration) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) : StageNineHolonomicConfiguration :=
  { background with matter := matter, conjugateMatter := dual }

def withMatter (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) : StageNineHolonomicConfiguration :=
  replaceMatter (TemporalGauge.configuration potential) matter dual

private theorem scalar_replace (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      (toContinuumPointField (replaceMatter background matter dual) point)
      (pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField (replaceMatter background matter dual) point) (temporalTest data)) =
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      (toContinuumPointField background point)
      (pointwiseScalarP286GaugeConnectionVariation (toContinuumPointField background point) (temporalTest data)) := rfl

private theorem scalar_readout (source readoutSource : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) (data : P286LieBlockData) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      (toContinuumPointField (formNativeP286GaugeConstitutiveReadout readoutSource background) point)
      (pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField (formNativeP286GaugeConstitutiveReadout readoutSource background) point)
          (temporalTest data)) =
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      (toContinuumPointField background point)
      (pointwiseScalarP286GaugeConnectionVariation (toContinuumPointField background point) (temporalTest data)) := rfl

theorem scalar_coefficient_preserved (potential : Potential)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    scalarGaugeConnectionKineticFirstVariationDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (withMatter potential matter dual) point)
      (pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField (withMatter potential matter dual) point) (temporalTest data)) =
      -scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point))/lapse^2 := by
  have original := charged_scalar_time potential point data
  rw [Stage10.Runtime.source_eq] at original ⊢
  unfold withMatter
  rw [scalar_replace, TemporalGauge.configuration, Stage10.Runtime.source_eq, scalar_readout]
  exact original

theorem matter_test (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    pointwiseMatterP286GaugeConnectionVariation
      (toContinuumPointField (withMatter potential matter dual) point) (temporalTest data) =
      fun direction => if direction = 0 then
        diracExteriorMotherLieAction (p286LieBlockEmbed data) (matter point) else 0 := by
  funext direction
  simp only [pointwiseMatterP286GaugeConnectionVariation, pointwiseP286GaugeConnectionMotherVariation,
    temporalTest, toContinuumPointField, withMatter, replaceMatter]
  split_ifs
  · simp only [LinearEquiv.symm_apply_apply]
  · simp [p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix]

theorem matter_time (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    matterGaugeConnectionFirstVariationDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (withMatter potential matter dual) point)
      (pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField (withMatter potential matter dual) point) (temporalTest data)) =
      lapse⁻¹ * (dual point (Stage9DEF.Compatibility.currentAction 0 data (matter point))).re := by
  rw [matter_test, Stage10.Runtime.source_eq]
  unfold matterGaugeConnectionFirstVariationDensity matterGaugeConnectionVariationVector
    matterGaugeKineticSum
  simp only [toContinuumPointField, withMatter, replaceMatter, matterDualFrameRelative_chartZero,
    matterDerivativeFrameRelative_zeroChart]
  have coframe : (TemporalGauge.configuration potential).coframe point = homogeneousCoframe lapse := by
    change Stage10.Runtime.configuration.coframe point = _
    rw [Stage10.Runtime.configuration_eq, actual_coframe]
  rw [coframe]
  simp only [Fin.sum_univ_four, show (1 : LorentzianIndex) ≠ 0 by decide,
    show (2 : LorentzianIndex) ≠ 0 by decide, show (3 : LorentzianIndex) ≠ 0 by decide,
    if_true, if_false, map_zero, add_zero]
  rw [homogeneousInverseGamma lapse lapse_pos.ne']
  simp only [coframeDiracMatrixMatterAction_smul_matrix]
  rw [smul_comm, map_smul]
  simp only [Stage9DEF.Compatibility.currentAction, LinearMap.smul_apply, LinearMap.comp_apply,
    smul_eq_mul, ite_true, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem charged_coefficient (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (data : P286LieBlockData) :
    formNativeChargedGaugeFirstCoefficient Stage10.Runtime.source 0 point
      (toContinuumPointField (withMatter potential matter dual) point) (temporalTest data) =
      -scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point))/lapse +
        (dual point (Stage9DEF.Compatibility.currentAction 0 data (matter point))).re := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [scalar_coefficient_preserved, matter_time]
  have volume : generatedVolumeDensity (toContinuumPointField (withMatter potential matter dual) point) = lapse := by
    change |(Stage10.Runtime.configuration.coframe point).det| = lapse
    rw [Stage10.Runtime.configuration_eq, actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  rw [volume]
  field_simp [lapse_pos.ne']

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedGauss
