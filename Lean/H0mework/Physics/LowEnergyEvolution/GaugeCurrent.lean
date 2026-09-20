import H0mework.Physics.LowEnergyEvolution.Gauge

/-! The complete charged covector of the moving primitive fields. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineTopologicalP286GaugeThreeFormDuality StageNineConnectionSectorSourceBalance
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open StageNineCoframeFirstJet StageNineCoframeLocalDifferentiability
open StageNineLorentzConnectionVariation
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory Response.Radial
noncomputable section

def spinCurrent (x : State) (mu : LorentzianIndex) (data : P286LieBlockData) : ℂ :=
  spinPairCurrentComplex mu data
    ((spinScale : ℂ) * (dilution (x 0) : ℂ) * Complex.exp (Complex.I * (x 6 : ℂ)))
    ((spinScale : ℂ) * (dilution (x 0) : ℂ) * Complex.exp (-Complex.I * (x 6 : ℂ)))
    ((dilution (x 0) : ℂ) * Complex.exp (Complex.I * (x 6 : ℂ)))
    ((dilution (x 0) : ℂ) * Complex.exp (-Complex.I * (x 6 : ℂ)))

private theorem phase_product (amplitude density angle : ℝ) :
    ((density : ℂ) * (amplitude : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) *
      ((amplitude : ℂ) * Complex.exp (-Complex.I * (angle : ℂ))) =
        ((density * amplitude^2 : ℝ) : ℂ) := by
  have phase : Complex.exp (Complex.I * (angle : ℂ)) * Complex.exp (-Complex.I * (angle : ℂ)) = 1 := by
    rw [← Complex.exp_add, show Complex.I * (angle : ℂ) + -Complex.I * (angle : ℂ) = 0 by ring,
      Complex.exp_zero]
  calc
    _ = ((density * amplitude^2 : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (angle : ℂ)) * Complex.exp (-Complex.I * (angle : ℂ))) := by
      push_cast
      ring
    _ = _ := by rw [phase, mul_one]

theorem spinCurrent_time (x : State) (data : P286LieBlockData) : spinCurrent x 0 data = 0 := by
  apply spinPairCurrentComplex_temporal_zero
  rw [phase_product]
  symm
  simpa only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg] using
    phase_product (dilution (x 0)) spinScale (-(x 6))

theorem spinCurrent_spatial (x : State) (axis : Fin 3) (data : P286LieBlockData) :
    (spinCurrent x axis.succ data).re =
      4 * spinScale * dilution (x 0)^2 * p286LiePairing (sourceColorP286Generator axis) data := by
  unfold spinCurrent
  rw [spinPairCurrentComplex_spatial_pairing axis data _ _ _ _
    (2*spinScale*dilution (x 0)^2) (by
      rw [phase_product, show ((spinScale : ℂ) * (dilution (x 0) : ℂ) *
          Complex.exp (-Complex.I * (x 6 : ℂ))) *
        ((dilution (x 0) : ℂ) * Complex.exp (Complex.I * (x 6 : ℂ))) =
          ((spinScale * dilution (x 0)^2 : ℝ) : ℂ) by
        simpa only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg] using
          phase_product (dilution (x 0)) spinScale (-(x 6))]
      push_cast
      ring)]
  ring

private theorem inverseGamma_current {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (mu : LorentzianIndex) (data : P286LieBlockData) :
    flow.configuration.conjugateMatter point (Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } mu)
      (diracExteriorMotherLieAction (p286LieBlockEmbed data) (flow.configuration.matter point))) =
      ((if mu = 0 then (clock (flow.pointState point))⁻¹ else (flow.pointState point 0)⁻¹ : ℝ) : ℂ) *
        spinCurrent (flow.pointState point) mu data := by
  have h : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [flow.coframe, diagonalInverseGamma _ _ (ne_of_gt (clock_positive _ h)) (ne_of_gt h.1)]
  change flow.configuration.conjugateMatter point (Complex.I • diracMatrixMatterAction
    (((if mu = 0 then (clock (flow.pointState point))⁻¹ else (flow.pointState point 0)⁻¹ : ℝ) : ℂ) • diracGamma mu)
    (diracExteriorMotherLieAction (p286LieBlockEmbed data) (flow.configuration.matter point))) = _
  rw [coframeDiracMatrixMatterAction_smul_matrix, smul_comm, map_smul]
  rfl

theorem Solution.matter_current {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource flow.configuration variation point =
      (4*clock (flow.pointState point)*spinScale/(flow.pointState point 0)) * ∑ axis : Fin 3,
        p286LiePairing (sourceColorP286Generator axis) (p286CoordinateEquiv.symm (variation axis.succ)) := by
  have h : Admissible (flow.pointState point) := flow.admissible _ inside
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart]
  change |(flow.configuration.coframe point).det| * (flow.configuration.conjugateMatter point
    (Complex.I • ∑ mu, diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } mu)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation mu)))
        (flow.configuration.matter point)))).re = _
  rw [Finset.smul_sum, map_sum, Complex.re_sum]
  simp_rw [inverseGamma_current flow point inside]
  rw [flow.coframe, diagonalCoframe_det, abs_of_pos (mul_pos (clock_positive _ h) (pow_pos h.1 3)),
    Fin.sum_univ_succ]
  simp only [ite_true, spinCurrent_time, mul_zero, Complex.zero_re, zero_add,
    Fin.succ_ne_zero, ite_false, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  simp_rw [spinCurrent_spatial]
  rw [dilution_square _ h.1]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  field_simp [ne_of_gt h.1]

theorem Solution.scalar_current_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : P286GaugeOneForm) :
    scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point)
      (pointwiseScalarP286GaugeConnectionVariation (toContinuumPointField flow.configuration point) variation) = 0 := by
  rw [flow.scalar_kinetic_first point inside]
  change _ * scalarCoordinatePairingRe
    (scalarMotherLieAction _ (direction + flow.pointState point 4 • direction)) direction = 0
  rw [scalarMotherLieAction_add_right, scalarMotherLieAction_real_smul_right,
    scalarCoordinatePairingRe_add_left, scalarCoordinatePairingRe_real_smul_left,
    radial_gauge_cross_zero, mul_zero, add_zero, mul_zero]

theorem Solution.charged_coefficient {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) variation =
      (4*clock (flow.pointState point)*spinScale/(flow.pointState point 0)) * ∑ axis : Fin 3,
        p286LiePairing (sourceColorP286Generator axis) (p286CoordinateEquiv.symm (variation axis.succ)) := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [flow.scalar_current_zero point inside, zero_add]
  exact flow.matter_current point inside variation

theorem Solution.charged_three_form {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) =
      (clock (flow.pointState point)/(lapse*flow.pointState point 0)) • chargedThreeForm := by
  rw [← actual_chargedThreeForm point]
  unfold formNativeChargedGaugeThreeForm p286GaugeThreeFormOfDual
  rw [← map_smul]
  congr 1
  apply LinearMap.ext
  intro variation
  change formNativeChargedGaugeFirstCoefficient _ _ _ _ _ =
    (clock (flow.pointState point)/(lapse*flow.pointState point 0)) *
      formNativeChargedGaugeFirstCoefficient _ _ _ _ _
  rw [flow.charged_coefficient point inside, actual_chargedCoefficient]
  field_simp [ne_of_gt lapse_pos]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
