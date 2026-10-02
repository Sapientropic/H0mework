import H0mework.Physics.Homogeneous.GaugeDifferential
import H0mework.Versions.R2.Physics.SpinPair.GaugeField
import H0mework.Physics.CoframeVariation.CoframeLocalVariation

/-! The complete original gauge coframe force on the same source actual.
The generated auxiliary is held fixed while the mother density is differentiated. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineBlockwiseConstitutive
open StageNineFormNativeMotherAction StageNineFormNativeGaugeWedge
open StageNineFormNativeGaugeAuxiliaryVariation StageNineP286GaugeAuxiliaryVariation
open StageNineTopologicalFourFormPairing StageNineDiracDualFormNativeCoframeLocalVariation
open SU7MotherLieAlgebra Stage9C.Dynamics.Homogeneous
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem sourceColor_orthogonal (first second : Fin 3) :
    formNativeP286LiePairing (sourceColorP286Generator first) (sourceColorP286Generator second) =
      if first = second then 1/2 else 0 := by
  change p286LiePairing (sourceColorP286Generator first) (sourceColorP286Generator second) = _
  rw [sourceColorP286Generator_pairing, sourceColorP286Generator_color]
  fin_cases first <;> fin_cases second <;> norm_num [sourceColorRaw]

private theorem uniformConstitutive_eq_lift
    (coframe : LorentzianCoframe) (coupling : ℝ) (form : Fin 6 → P286LieBlockData) :
    formNativeP286BlockwiseConstitutive coframe coupling coupling coupling form =
      liftGaugeTwoFormOperator (coupling • coframeGaugeSpacetimeHodgeLinear coframe) form := by
  funext output
  simp only [formNativeP286BlockwiseConstitutive, liftGaugeTwoFormOperator, Fin.sum_univ_six]
  rfl

private theorem sourceAuxiliary_quadratic (clock amplitude : ℝ) (coframe : LorentzianCoframe) :
    formNativeP286GaugeWedgeCoefficient (electricAuxiliary clock amplitude)
      (formNativeP286BlockwiseConstitutive coframe sourceCoupling sourceCoupling sourceCoupling
        (electricAuxiliary clock amplitude)) =
      sourceCoupling * (amplitude^2/(sourceCoupling*clock))^2 / 2 * magneticHodgeTrace coframe := by
  have zeroRight (data : P286LieBlockData) : formNativeP286LiePairing data 0 = 0 :=
    (formNativeP286LiePairingBilinear data).map_zero
  have zeroLeft (data : P286LieBlockData) : formNativeP286LiePairing 0 data = 0 := by
    rw [formNativeP286LiePairing_symmetric, zeroRight]
  rw [uniformConstitutive_eq_lift]
  unfold formNativeP286GaugeWedgeCoefficient generatedTwoFormWedgeCoefficient
    liftGaugeTwoFormOperator
  simp [Fin.sum_univ_six, twoFormComplement, electricAuxiliary,
    formNativeP286LiePairing_add_right, formNativeP286LiePairing_smul_left,
    formNativeP286LiePairing_smul_right, zeroLeft, sourceColor_orthogonal,
    gaugeOperatorCoefficient, magneticHodgeTrace]
  ring

theorem actual_gaugeDensity_coframe (point : BasePoint) (coframe : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
      (toContinuumPointField actual point) coframe =
      formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary point)
        (holonomicGaugeCurvature actual point) -
      sourceCoupling * (gaugeScale^2/(sourceCoupling*lapse))^2 / 4 * magneticHodgeTrace coframe := by
  unfold diracDualFormNativeCoframeGaugeDensity
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  change formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary point)
      (holonomicGaugeCurvature actual point) - (1/2:ℝ) *
      formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary point)
        (formNativeP286BlockwiseConstitutive coframe sourceCoupling sourceCoupling sourceCoupling
          (actual.gaugeAuxiliary point)) = _
  simp only [actual_gaugeAuxiliary, sourceAuxiliary_quadratic]
  ring

theorem actual_gaugeCoframe (point : BasePoint) (direction : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
      (toContinuumPointField actual point) direction =
      gaugeScale^4 / (4*sourceCoupling*lapse^2) *
        (3*direction 0 0 - lapse*(direction 1 1 + direction 2 2 + direction 3 3)) := by
  have derivative := diracDualFormNativeCoframeGaugeDensity_hasFDerivAt
    positiveSmoothUnifiedSource (toContinuumPointField actual point) (actual_nondegenerate point)
  have center : (toContinuumPointField actual point).coframe = homogeneousCoframe lapse :=
    congrFun actual_coframe point
  rw [center] at derivative
  have derivative' : HasFDerivAt
      (diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource (toContinuumPointField actual point))
      (diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
        (toContinuumPointField actual point))
      (homogeneousCoframe lapse + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using derivative
  have evaluated := derivative'.comp_hasDerivAt 0
    (coframe_line_hasDerivAt (homogeneousCoframe lapse) direction)
  let coefficient := sourceCoupling * (gaugeScale^2/(sourceCoupling*lapse))^2 / 4
  have computed : HasDerivAt
      (fun t : ℝ => diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        (toContinuumPointField actual point) (homogeneousCoframe lapse + t • direction))
      (-(coefficient * (lapse*(direction 1 1 + direction 2 2 + direction 3 3) - 3*direction 0 0))) 0 := by
    simp_rw [actual_gaugeDensity_coframe]
    exact ((magneticHodgeTrace_line_hasDerivAt lapse lapse_pos direction).const_mul coefficient).const_sub
      (formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary point)
        (holonomicGaugeCurvature actual point))
  have observed := evaluated.unique computed
  have coefficient_eq : coefficient = gaugeScale^4 / (4*sourceCoupling*lapse^2) := by
    dsimp [coefficient]
    field_simp [ne_of_gt lapse_pos, sourceCoupling_eq]
  change diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
    (toContinuumPointField actual point) direction = _ at observed
  rw [observed, coefficient_eq]
  ring

theorem actual_gaugeCoframe_coordinates (point : BasePoint) (row column : LorentzianIndex) :
    diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
      (toContinuumPointField actual point) (Matrix.single row column 1) =
      if row = column then
        if row = 0 then 3*gaugeScale^4/(4*sourceCoupling*lapse^2)
        else -gaugeScale^4/(4*sourceCoupling*lapse)
      else 0 := by
  rw [actual_gaugeCoframe]
  fin_cases row <;> fin_cases column <;> simp
  all_goals field_simp [ne_of_gt lapse_pos]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
