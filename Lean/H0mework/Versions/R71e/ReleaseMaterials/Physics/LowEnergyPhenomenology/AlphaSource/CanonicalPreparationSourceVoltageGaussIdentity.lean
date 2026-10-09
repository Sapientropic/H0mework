import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageWholeForcing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumVoltageGaussGreen
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineCanonicalCauchyState
open StageNineCoframeLocalDifferentiability StageNineP286ActionCauchySplit
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineP286GaugeConnectionVariation StageNineTopologicalP286GaugeThreeFormDuality
open StageNineP286GaugeAuxiliaryVariation StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage10
open PreparationVacuumMixedFieldReturn PreparationCoordinates
open PreparationVacuumStaticVoltageSource SourcePropagationNativeActionHessian
open SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open SourcePropagationMotherResidualDirections
open scoped Topology ContDiff BigOperators
attribute [local irreducible] Runtime.configuration Runtime.source nativeEuler nativeConfiguration

/-- Original current of the identical background, with its independent dual. -/
def sourceVoltageBaseCurrent (space : StageNineSpatialPoint) : ℝ :=
  (Runtime.configuration.conjugateMatter (canonicalCauchySlicePoint 0 space)
    (Stage9DEF.Compatibility.currentAction 0 HyperchargeResponse.chargeDirection
      (Runtime.configuration.matter (canonicalCauchySlicePoint 0 space)))).re

private theorem replace_self (c : StageNineHolonomicConfiguration) :
    ChargedGauss.replaceMatter c c.matter c.conjugateMatter=c := by
  cases c
  rfl

private theorem same_configuration (profile : BasePoint→ℝ) (a : ℝ) :
    CanonicalGauss.withMatter (CanonicalGauss.abelianPotential (fun x=>a*profile x))
      Runtime.configuration.matter Runtime.configuration.conjugateMatter=sourceVoltageConfiguration profile a := by
  have same:=replace_self (sourceVoltageConfiguration profile a)
  rw [(sourceVoltage_matter profile a).1,(sourceVoltage_matter profile a).2] at same
  exact same

private theorem regular_profile (profile : BasePoint→ℝ) (smooth : ContDiff ℝ ∞ profile) :
    CanonicalGauss.ScalarRegular profile := by
  refine ⟨smooth.differentiable (by simp),fun axis=>?_⟩
  exact ((smooth.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)

private theorem laplacian_scale (profile : BasePoint→ℝ) (regular : CanonicalGauss.ScalarRegular profile)
    (a : ℝ) (point : BasePoint) :
    CanonicalGauss.spatialLaplacian (fun x=>a*profile x) point=a*CanonicalGauss.spatialLaplacian profile point := by
  have derivative (p : BasePoint) (mu : Fin 4) :
      fieldDirectionalDerivative (fun x=>a*profile x) p mu=a*fieldDirectionalDerivative profile p mu := by
    unfold fieldDirectionalDerivative
    rw [fderiv_const_mul (regular.1 p)]
    rfl
  simp only [CanonicalGauss.spatialLaplacian,derivative]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro axis _
  have generated:=congrArg (fun derivative=>derivative (coordinateDirection axis.succ))
    ((regular.2 axis point).hasFDerivAt.const_mul a).fderiv
  simpa only [fieldDirectionalDerivative,smul_apply,smul_eq_mul] using generated

/-- Finite voltage amplitude, full original Gauss form and original matter current on the same nine-group configuration. -/
theorem sourceVoltage_originalGauss (profile : BasePoint→ℝ) (smooth : ContDiff ℝ ∞ profile)
    (a : ℝ) (space : StageNineSpatialPoint) :
    p286CoordinateLiePairing (p286CoordinateEquiv HyperchargeResponse.chargeDirection)
      (holonomicFormNativeP286GaugeEulerThreeForm Runtime.source 0
        (nativeConfiguration (sourceVoltageSignal profile a)) (canonicalCauchySlicePoint 0 space) 3)=
      -(2*lapse)*a*CanonicalGauss.spatialLaplacian profile (canonicalCauchySlicePoint 0 space)+sourceVoltageBaseCurrent space := by
  rw [sourceVoltage_nativeConfiguration profile (smooth.differentiable (by simp)),←same_configuration]
  have scaled : ContDiff ℝ ∞ (fun x=>a*profile x):=contDiff_const.mul smooth
  rw [CanonicalGauss.poisson_gauss _ (regular_profile _ scaled),laplacian_scale _ (regular_profile _ smooth)]
  unfold sourceVoltageBaseCurrent
  ring

private theorem native_voltage_direction : fieldGauge (Pi.single 20 1 : Field289)=
    fun mu=>if mu=0 then p286CoordinateEquiv HyperchargeResponse.chargeDirection else 0 := by
  funext mu
  fin_cases mu <;> simp [fieldGauge,gaugeSlot,Pi.single_apply,Fin.sum_univ_succ,sourceVoltageY_native]

private theorem temporal_wedge (three : Fin 4→P286CoordinateCarrier) :
    p286GaugeOneFormThreeFormWedgeCoefficient (fieldGauge (Pi.single 20 1 : Field289)) three=
      p286CoordinateLiePairing (p286CoordinateEquiv HyperchargeResponse.chargeDirection) (three 3) := by
  rw [native_voltage_direction]
  simp [p286GaugeOneFormThreeFormWedgeCoefficient,Fin.sum_univ_four,
    oneWedgeThreeSign,missingTripleOfOneForm,p286CoordinateLiePairing,
    p286LiePairing,specialUnitaryLiePairing,hyperchargeLiePairing]

private theorem native_gauss (profile : BasePoint→ℝ) (smooth : ContDiff ℝ ∞ profile)
    (a : ℝ) (space : StageNineSpatialPoint)
    (inside : signalFirstJet (sourceVoltageSignal profile a) (canonicalCauchySlicePoint 0 space)∈nativeEulerSourceDomain) :
    nativeHolonomicEuler (sourceVoltageSignal profile a) (canonicalCauchySlicePoint 0 space) 20=
      -(2*lapse)*a*CanonicalGauss.spatialLaplacian profile (canonicalCauchySlicePoint 0 space)+sourceVoltageBaseCurrent space := by
  have regular:=sourceVoltageSignal_smooth profile smooth a
  rw [nativeGaugeEuler_identification _ _ (motherSignalC2 _ regular _) (nativeConfiguration_source_smooth _ regular) inside 20 (by norm_num),temporal_wedge]
  rw [nativeEuler_original]
  change p286CoordinateLiePairing _ (holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
    (nativeConfiguration (sourceVoltageSignal profile a)) (canonicalCauchySlicePoint 0 space) 3)=_
  rw [←Runtime.source_eq]
  exact sourceVoltage_originalGauss profile smooth a space

/-- Admissibility is generated by the actual first-jet ray near zero amplitude. -/
theorem sourceVoltage_Gauss_eventually (profile : BasePoint→ℝ) (smooth : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint) :
    (fun a : ℝ=>nativeHolonomicEuler (sourceVoltageSignal profile a) (canonicalCauchySlicePoint 0 space) 20)=ᶠ[nhds 0]
      fun a=>-(2*lapse)*a*CanonicalGauss.spatialLaplacian profile (canonicalCauchySlicePoint 0 space)+sourceVoltageBaseCurrent space := by
  let point:=canonicalCauchySlicePoint 0 space
  let jet:=signalFirstJet (sourceVoltageSignal profile 1) point
  have continuous : Continuous (fun a : ℝ=>a • jet):=continuous_id.smul continuous_const
  have near : ∀ᶠ a : ℝ in nhds 0,a • jet∈nativeEulerSourceDomain :=
    (continuous.continuousAt (x:=0)).eventually_mem (by simpa only [zero_smul] using nativeEulerSourceDomain_generated)
  filter_upwards [near] with a ha
  apply native_gauss profile smooth a space
  rw [sourceVoltageSignal_amplitude profile a,signalFirstJet_smul]
  · exact ha
  · exact (sourceVoltageSignal_smooth profile smooth 1).differentiable (by simp) |>.differentiableAt

/-- The original form-native Poisson law and full native-action Euler now yield the same voltage response. -/
theorem sourceVoltage_Gauss_derivative (profile : BasePoint→ℝ) (smooth : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint) :
    HasDerivAt (fun a : ℝ=>nativeHolonomicEuler (sourceVoltageSignal profile a) (canonicalCauchySlicePoint 0 space) 20)
      (-(2*lapse)*CanonicalGauss.spatialLaplacian profile (canonicalCauchySlicePoint 0 space)) 0 := by
  have h:=(((hasDerivAt_id (0:ℝ)).const_mul (-(2*lapse))).mul_const
    (CanonicalGauss.spatialLaplacian profile (canonicalCauchySlicePoint 0 space))).add_const (sourceVoltageBaseCurrent space)
  simpa using h.congr_of_eventuallyEq (sourceVoltage_Gauss_eventually profile smooth space)

end LowEnergy.PreparationVacuumVoltageGaussGreen
