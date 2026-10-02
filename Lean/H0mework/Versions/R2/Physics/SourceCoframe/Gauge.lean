import H0mework.Versions.R2.Physics.SourceGauge.Material
import H0mework.Physics.Homogeneous.GaugeDifferential

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineBlockwiseConstitutive
open StageNineFormNativeMotherAction StageNineFormNativeGaugeWedge
open StageNineFormNativeGaugeAuxiliaryVariation StageNineP286GaugeAuxiliaryVariation
open StageNineTopologicalFourFormPairing StageNineDiracDualFormNativeCoframeLocalVariation
open SU7MotherLieAlgebra Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous Gauge
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem color_orthogonal (first second : Fin 3) :
    formNativeP286LiePairing (sourceColorP286Generator first) (sourceColorP286Generator second) =
      if first = second then 1/2 else 0 := by
  change p286LiePairing (sourceColorP286Generator first) (sourceColorP286Generator second) = _
  rw [sourceColorP286Generator_pairing, sourceColorP286Generator_color]
  fin_cases first <;> fin_cases second <;> norm_num [sourceColorRaw]

private theorem uniform_constitutive
    (coframe : LorentzianCoframe) (coupling : ℝ) (form : Fin 6 → P286LieBlockData) :
    formNativeP286BlockwiseConstitutive coframe coupling coupling coupling form =
      liftGaugeTwoFormOperator (coupling • coframeGaugeSpacetimeHodgeLinear coframe) form := by
  funext output
  simp only [formNativeP286BlockwiseConstitutive, liftGaugeTwoFormOperator, Fin.sum_univ_six]
  rfl

theorem auxiliary_quadratic (step : ℕ) (coframe : LorentzianCoframe) :
    formNativeP286GaugeWedgeCoefficient (electric step)
      (formNativeP286BlockwiseConstitutive coframe (coupling step) (coupling step) (coupling step)
        (electric step)) =
      coupling step * auxiliaryScale step^2 / 2 * magneticHodgeTrace coframe := by
  have zeroRight (data : P286LieBlockData) : formNativeP286LiePairing data 0 = 0 :=
    (formNativeP286LiePairingBilinear data).map_zero
  have zeroLeft (data : P286LieBlockData) : formNativeP286LiePairing 0 data = 0 := by
    rw [formNativeP286LiePairing_symmetric, zeroRight]
  rw [uniform_constitutive]
  unfold formNativeP286GaugeWedgeCoefficient generatedTwoFormWedgeCoefficient
    liftGaugeTwoFormOperator
  simp [Fin.sum_univ_six, twoFormComplement, electric,
    formNativeP286LiePairing_add_right, formNativeP286LiePairing_smul_left,
    formNativeP286LiePairing_smul_right, zeroLeft, color_orthogonal,
    gaugeOperatorCoefficient, magneticHodgeTrace]
  ring

theorem gauge_density (step : ℕ) (point : BasePoint) (coframe : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeDensity (sourceAt step)
      (toContinuumPointField (fieldAt step) point) coframe =
      formNativeP286GaugeWedgeCoefficient ((fieldAt step).gaugeAuxiliary point)
        (holonomicGaugeCurvature (fieldAt step) point) -
      coupling step * auxiliaryScale step^2 / 4 * magneticHodgeTrace coframe := by
  unfold diracDualFormNativeCoframeGaugeDensity
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  simp only [(source_couplings step).1, (source_couplings step).2.1,
    (source_couplings step).2.2]
  change formNativeP286GaugeWedgeCoefficient ((fieldAt step).gaugeAuxiliary point)
      (holonomicGaugeCurvature (fieldAt step) point) - (1/2:ℝ) *
      formNativeP286GaugeWedgeCoefficient ((fieldAt step).gaugeAuxiliary point)
        (formNativeP286BlockwiseConstitutive coframe (coupling step) (coupling step) (coupling step)
          ((fieldAt step).gaugeAuxiliary point)) = _
  simp only [field_auxiliary, auxiliary_quadratic]
  ring

theorem gauge_coframe (step : ℕ) (point : BasePoint) (direction : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeEulerCovector (sourceAt step)
      (toContinuumPointField (fieldAt step) point) direction =
      gaugeScale^4 / (4*coupling step*clock step^2) *
        (3*direction 0 0 - clock step*(direction 1 1 + direction 2 2 + direction 3 3)) := by
  have derivative := diracDualFormNativeCoframeGaugeDensity_hasFDerivAt
    (sourceAt step) (toContinuumPointField (fieldAt step) point) (field_nondegenerate step point)
  have center : (toContinuumPointField (fieldAt step) point).coframe = homogeneousCoframe (clock step) :=
    congrFun (field_coframe step) point
  rw [center] at derivative
  have derivative' : HasFDerivAt
      (diracDualFormNativeCoframeGaugeDensity (sourceAt step) (toContinuumPointField (fieldAt step) point))
      (diracDualFormNativeCoframeGaugeEulerCovector (sourceAt step)
        (toContinuumPointField (fieldAt step) point))
      (homogeneousCoframe (clock step) + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using derivative
  have evaluated := derivative'.comp_hasDerivAt 0
    (coframe_line_hasDerivAt (homogeneousCoframe (clock step)) direction)
  let coefficient := coupling step * auxiliaryScale step^2 / 4
  have computed : HasDerivAt
      (fun t : ℝ => diracDualFormNativeCoframeGaugeDensity (sourceAt step)
        (toContinuumPointField (fieldAt step) point) (homogeneousCoframe (clock step) + t • direction))
      (-(coefficient * (clock step*(direction 1 1 + direction 2 2 + direction 3 3) - 3*direction 0 0))) 0 := by
    simp_rw [gauge_density]
    exact ((magneticHodgeTrace_line_hasDerivAt (clock step) (clock_pos step) direction).const_mul
      coefficient).const_sub (formNativeP286GaugeWedgeCoefficient ((fieldAt step).gaugeAuxiliary point)
        (holonomicGaugeCurvature (fieldAt step) point))
  have observed := evaluated.unique computed
  have coefficient_eq : coefficient = gaugeScale^4 / (4*coupling step*clock step^2) := by
    dsimp [coefficient, auxiliaryScale]
    field_simp [ne_of_gt (clock_pos step), ne_of_gt (coupling_pos step)]
  change diracDualFormNativeCoframeGaugeEulerCovector (sourceAt step)
    (toContinuumPointField (fieldAt step) point) direction = _ at observed
  rw [observed, coefficient_eq]
  ring

theorem gauge_coordinates (step : ℕ) (point : BasePoint) (row column : LorentzianIndex) :
    diracDualFormNativeCoframeGaugeEulerCovector (sourceAt step)
      (toContinuumPointField (fieldAt step) point) (Matrix.single row column 1) =
      if row = column then
        if row = 0 then 3*gaugeScale^4/(4*coupling step*clock step^2)
        else -gaugeScale^4/(4*coupling step*clock step)
      else 0 := by
  rw [gauge_coframe]
  fin_cases row <;> fin_cases column <;> simp
  all_goals field_simp [ne_of_gt (clock_pos step)]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe
