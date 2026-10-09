import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPhysicalCarrierGauss

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMPhysicalCarrier
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction
open StageNineP286GaugeAuxiliaryVariation StageNineCoframeLocalDifferentiability
open StageNineCanonicalCauchyState StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeGaugeWedge StageNineFormNativeMotherAction
open StageNineEnrichedProofFreeSource StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open Stage9C.Material.SpinPair Stage10 TemporalGauge CanonicalGauss PhysicalEMGaugeRealization
open scoped BigOperators
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

private theorem color_pair (i j : Fin 3) :
    p286LiePairing (sourceColorP286Generator i) (sourceColorP286Generator j) =
      if i = j then 1/2 else 0 := by
  rw [sourceColorP286Generator_pairing, sourceColorP286Generator_color]
  fin_cases i <;> fin_cases j <;> norm_num [sourceColorRaw]

private theorem color_y (i : Fin 3) :
    p286LiePairing (sourceColorP286Generator i) HyperchargeResponse.chargeDirection = 0 := by
  rw [sourceColorP286Generator_pairing]
  fin_cases i <;> norm_num [HyperchargeResponse.chargeDirection]

private theorem y_color (i : Fin 3) :
    p286LiePairing HyperchargeResponse.chargeDirection (sourceColorP286Generator i) = 0 := by
  rw [p286LiePairing_symmetric, color_y]

private theorem em_split : emDirection =
    (-1 : ℝ) • sourceColorP286Generator 2 + (-1/2 : ℝ) • HyperchargeResponse.chargeDirection := by
  unfold emDirection
  module

private theorem em_color (i : Fin 3) :
    p286LiePairing emDirection (sourceColorP286Generator i) = if i = 2 then -1/2 else 0 := by
  rw [em_split, p286LiePairing_add_left, p286LiePairing_smul_left, p286LiePairing_smul_left,
    color_pair, y_color]
  by_cases h : i = 2
  · subst i
    simp
    norm_num
  · simp [h, Ne.symm h]

private theorem color_em (i : Fin 3) :
    p286LiePairing (sourceColorP286Generator i) emDirection = if i = 2 then -1/2 else 0 := by
  rw [p286LiePairing_symmetric, em_color]

private theorem em_y : p286LiePairing emDirection HyperchargeResponse.chargeDirection = -1/2 := by
  rw [em_split, p286LiePairing_add_left, p286LiePairing_smul_left,
    p286LiePairing_smul_left, color_y, charge_pairing]
  norm_num

private theorem y_em : p286LiePairing HyperchargeResponse.chargeDirection emDirection = -1/2 := by
  rw [p286LiePairing_symmetric, em_y]

private theorem em_pair : p286LiePairing emDirection emDirection = 3/4 := by
  conv_lhs => arg 1; rw [em_split]
  rw [p286LiePairing_add_left, p286LiePairing_smul_left,
    p286LiePairing_smul_left, color_em, y_em]
  norm_num

/-- This coefficient is the original electric quadratic form on the generated EM Cauchy field. -/
theorem em_cauchy_electric_energy (V : BasePoint → ℝ) (x : BasePoint)
    (hV : DifferentiableAt ℝ V x) :
    squared (electric (emPotential V) x) =
      (3/4 : ℝ)*(∑ i : Fin 3, (fieldDirectionalDerivative V x i.succ)^2) +
      gaugeScale^2*(V x)^2 := by
  rw [em_cauchy_electric V x hV]
  simp only [squared, Fin.sum_univ_three]
  change p286LiePairing
    ((-fieldDirectionalDerivative V x 1) • emDirection+(gaugeScale*V x) • sourceColorP286Generator 1)
    ((-fieldDirectionalDerivative V x 1) • emDirection+(gaugeScale*V x) • sourceColorP286Generator 1) +
    p286LiePairing
    ((-fieldDirectionalDerivative V x 2) • emDirection+(-gaugeScale*V x) • sourceColorP286Generator 0)
    ((-fieldDirectionalDerivative V x 2) • emDirection+(-gaugeScale*V x) • sourceColorP286Generator 0) +
    p286LiePairing ((-fieldDirectionalDerivative V x 3) • emDirection)
      ((-fieldDirectionalDerivative V x 3) • emDirection) =
    (3/4 : ℝ)*((fieldDirectionalDerivative V x 1)^2+(fieldDirectionalDerivative V x 2)^2+
      (fieldDirectionalDerivative V x 3)^2)+gaugeScale^2*(V x)^2
  simp only [p286LiePairing_add_left, p286LiePairing_add_right,
    p286LiePairing_smul_left, p286LiePairing_smul_right, em_pair, em_color, color_em, color_pair]
  norm_num [Fin.ext_iff]
  ring

private theorem gauge_density_normal (s : SmoothUnifiedSource) (c : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings s)
      (toContinuumPointField (ChargedGauss.replaceMatter
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator c) matter dual) x) =
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings s)
      (toContinuumPointField c x) := rfl

/-- The constitutive B field and electric energy are evaluated on the same scalar-dressed event. -/
theorem em_cauchy_gauge_density (V : BasePoint → ℝ) (x : BasePoint)
    (hV : DifferentiableAt ℝ V x)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings Stage10.Runtime.source)
      (toContinuumPointField (emCauchyField V matter dual) x) =
      lapse*((3/4 : ℝ)*(∑ i : Fin 3, (fieldDirectionalDerivative V x i.succ)^2) +
        gaugeScale^2*(V x)^2) - lapse⁻¹*squared magnetic := by
  unfold emCauchyField CanonicalGauss.withMatter CanonicalGauss.configuration
  rw [gauge_density_normal, gauge_density, em_cauchy_electric_energy V x hV]

def emCauchyGaussRead (V : BasePoint → ℝ)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint)
    (a : P286LieBlockData) : ℝ :=
  p286CoordinateLiePairing (p286CoordinateEquiv a)
    (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
      (emCauchyField V matter dual) (canonicalCauchySlicePoint 0 x) 3)

def emCauchyMatterRead (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint)
    (a : P286LieBlockData) : ℝ :=
  (dual (canonicalCauchySlicePoint 0 x) (Stage9DEF.Compatibility.currentAction 0 a
    (matter (canonicalCauchySlicePoint 0 x)))).re

/-- The EM equation retains the original background term and the full independent-dual current. -/
theorem em_cauchy_em_gauss (V : BasePoint → ℝ) (hV : ScalarRegular V)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint) :
    emCauchyGaussRead V matter dual x emDirection =
      -(3*lapse/2)*spatialLaplacian V (canonicalCauchySlicePoint 0 x) +
      2*lapse*gaugeScale^2*V (canonicalCauchySlicePoint 0 x) +
      emCauchyMatterRead matter dual x emDirection := by
  unfold emCauchyGaussRead
  rw [em_cauchy_gauss V hV]
  simp only [p286LiePairing_add_right, p286LiePairing_smul_right, em_pair, em_color]
  norm_num [Fin.ext_iff]
  unfold emCauchyMatterRead
  ring

/-- The other three rows close the color-plus-hypercharge span; a single EM projection does not erase them. -/
theorem em_cauchy_mixed_gauss (V : BasePoint → ℝ) (hV : ScalarRegular V)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint) :
    emCauchyGaussRead V matter dual x (sourceColorP286Generator 0) =
      -2*lapse*gaugeScale*fieldDirectionalDerivative V (canonicalCauchySlicePoint 0 x) 2 +
        emCauchyMatterRead matter dual x (sourceColorP286Generator 0) ∧
    emCauchyGaussRead V matter dual x (sourceColorP286Generator 1) =
      2*lapse*gaugeScale*fieldDirectionalDerivative V (canonicalCauchySlicePoint 0 x) 1 +
        emCauchyMatterRead matter dual x (sourceColorP286Generator 1) ∧
    emCauchyGaussRead V matter dual x HyperchargeResponse.chargeDirection =
      lapse*spatialLaplacian V (canonicalCauchySlicePoint 0 x) +
        emCauchyMatterRead matter dual x HyperchargeResponse.chargeDirection := by
  constructor
  · unfold emCauchyGaussRead
    rw [em_cauchy_gauss V hV]
    simp only [p286LiePairing_add_right, p286LiePairing_smul_right, color_pair, color_em]
    norm_num [Fin.ext_iff]
    unfold emCauchyMatterRead
    ring
  constructor
  · unfold emCauchyGaussRead
    rw [em_cauchy_gauss V hV]
    simp only [p286LiePairing_add_right, p286LiePairing_smul_right, color_pair, color_em]
    norm_num [Fin.ext_iff]
    unfold emCauchyMatterRead
    ring
  · unfold emCauchyGaussRead
    rw [em_cauchy_gauss V hV]
    simp only [p286LiePairing_add_right, p286LiePairing_smul_right, y_color, y_em]
    unfold emCauchyMatterRead
    ring

end LowEnergy.GaussComposite.ActualEMPhysicalCarrier
