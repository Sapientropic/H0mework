import H0mework.Physics.LowEnergyEvolution.Fields
import H0mework.Physics.Homogeneous.CartanSource

/-! The original W13 source response determines the moving Cartan coefficient.
The scale factor enters both the coframe and the actual two-sided spin pairing. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineCoframeFirstJet StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine StageNineP286GaugeConnectionVariationDensity
open StageNineMatterVariation StageNineCoframeLocalDifferentiability
open StageNineFormNativeMatterSpinThreeForm StageNineFormNativeLorentzGeometricFirstVariation
open StageNineTopologicalLorentzThreeFormDuality StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeSpinTorsionAcceptance StageNineIIPlusRestriction
open StageNineCartanAffineConnectionActualization StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormEquiv StageNineCartanTorsionThreeFormCoordinates
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
noncomputable section

theorem diagonalCoframe_inv (n a : ℝ) (hn : n ≠ 0) (ha : a ≠ 0) :
    (diagonalCoframe n a)⁻¹ = diagonalCoframe n⁻¹ a⁻¹ := by
  apply Matrix.inv_eq_left_inv
  unfold diagonalCoframe
  rw [Matrix.diagonal_mul_diagonal]
  ext row col
  fin_cases row <;> fin_cases col <;> simp [hn, ha]

private def spinField (n a : ℝ) (u v p q : ℂ) : StageNineContinuumPointField :=
  { homogeneousSpinField n u v p q with coframe := diagonalCoframe n a }

private def spinCoefficient (density : ℝ) (mu : LorentzianIndex) (pair : Fin 6) : ℝ :=
  if (mu = 1 ∧ pair = 3) ∨ (mu = 2 ∧ pair = 4) ∨ (mu = 3 ∧ pair = 5) then -2*density else 0

private theorem spin_triple (u v p q : ℂ) (density : ℝ)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ))
    (mu : LorentzianIndex) (pair : Fin 6) :
    (Complex.I * (2 : ℂ)⁻¹ * spinPairDual p q
      (diracMatrixMatterAction (diracGamma mu * (diracGamma (pairFirst pair) * diracGamma (pairSecond pair)))
        (spinPairMatter u v))).re = spinCoefficient density mu pair := by
  rw [spinPairDual_diracMatrix, pv, qu]
  fin_cases mu <;> fin_cases pair <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, pairFirst, pairSecond,
      spinCoefficient, Complex.mul_re, Complex.mul_im] <;> ring

theorem diagonalInverseGamma (n a : ℝ) (hn : n ≠ 0) (ha : a ≠ 0) (mu : LorentzianIndex) :
    inverseCoframeDiracGamma { coframe := diagonalCoframe n a, derivative := 0 } mu =
      (if mu = 0 then n⁻¹ else a⁻¹ : ℝ) • diracGamma mu := by
  unfold inverseCoframeDiracGamma
  rw [diagonalCoframe_inv n a hn ha]
  fin_cases mu <;> simp [diagonalCoframe, Fin.sum_univ_four]

private theorem spinField_coefficient (n a density : ℝ) (hn : 0 < n) (ha : 0 < a)
    (u v p q : ℂ) (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ))
    (point : BasePoint) (mu : LorentzianIndex) (pair : Fin 6) :
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
      (spinField n a u v p q) (loweredLorentzBivectorOneFormCoordinate mu pair) =
      n*a^2 * spinCoefficient density mu pair := by
  unfold formNativeLorentzMatterFirstCoefficient matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
  simp only [matterDualFrameRelative_chartZero, matterDerivativeFrameRelative_zeroChart,
    spinField, homogeneousSpinField, Stage9C.Dynamics.PlaneWave.spinLift_coordinate]
  rw [Finset.sum_eq_single mu]
  · simp only [ite_true, map_smul]
    rw [Stage9C.Dynamics.PlaneWave.matrixAction_comp, diagonalInverseGamma n a (ne_of_gt hn) (ne_of_gt ha)]
    simp only [Matrix.smul_mul]
    unfold generatedVolumeDensity
    rw [diagonalCoframe_det, abs_of_pos (mul_pos hn (pow_pos ha 3))]
    simp only [Matrix.mul_smul, diracMatrixMatterAction_real_smul_matrix_local,
      coframeDiracMatrixMatterAction_smul_matrix, (spinPairDual p q).map_smul_of_tower, smul_eq_mul]
    have realRead (r : ℝ) (z : ℂ) :
        (Complex.I * (r • ((2 : ℂ)⁻¹ * z))).re = r * (Complex.I * (2 : ℂ)⁻¹ * z).re := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [realRead, spin_triple u v p q density pv qu]
    by_cases temporal : mu = 0
    · subst mu
      simp [spinCoefficient]
    · rw [if_neg temporal]
      field_simp [ne_of_gt ha]
  · intro other _ different
    simp [different]
  · simp

private def spinTorsion (a density : ℝ) : PointwiseCartanTorsionTwoForm :=
  ⟨!![0,0,0,0;0,0,0,0;0,0,0,0;
      0,-2*a^2*density,0,0;0,0,-2*a^2*density,0;0,0,0,-2*a^2*density]⟩

private theorem spinContorsion_torsion (n a density : ℝ) :
    actualCartanTorsionIncrementTwoForm (diagonalCoframe n a)
      (homogeneousContorsion (a*density)) = spinTorsion a density := by
  ext pair internal
  simp only [actualCartanTorsionIncrementTwoForm, actualPointwiseCartanTorsionTwoForm,
    pointwiseCartanTorsion, pointwiseCoframeCovariantDerivative, coframeConnectionAction,
    Pi.zero_apply, zero_add]
  fin_cases pair <;> fin_cases internal <;>
    simp [diagonalCoframe, homogeneousContorsion, spinTorsion, lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] <;> ring

private theorem spinContorsion_generates (n a density : ℝ) (hn : 0 < n) (ha : 0 < a)
    (u v p q : ℂ) (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) (point : BasePoint) :
    cartanTorsionThreeForm (diagonalCoframe n a)
      (cartanTorsionOfContorsion (diagonalCoframe n a) (homogeneousContorsion (a*density))) =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 point (spinField n a u v p q) := by
  have nonzero : (diagonalCoframe n a).det ≠ 0 := by
    rw [diagonalCoframe_det]
    exact mul_ne_zero (ne_of_gt hn) (pow_ne_zero _ (ne_of_gt ha))
  rw [← actualCartanTorsionIncrementTwoForm_eq_factored _ nonzero, spinContorsion_torsion]
  funext pair triple
  change _ = -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
      (spinField n a u v p q)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) pair))
  rw [spinField_coefficient n a density hn ha u v p q pv qu point]
  fin_cases pair <;> fin_cases triple <;>
    simp [cartanTorsionThreeForm, cartanTorsionCoframeWedgeThreeForm,
      rawPointwiseCartanTorsion, orderedCartanTorsionComponent,
      internalBivectorDualThreeForm, torsionCoframeWedgeThreeForm,
      spinTorsion, spinCoefficient, diagonalCoframe,
      orientedLorentzBivectorBasisCoefficient, lorentzianCoframeHodge,
      pairFirst, pairSecond, threeFormFirst, threeFormSecond, threeFormThird,
      oneWedgeThreeSign, missingTripleOfOneForm, Fin.sum_univ_six] <;> ring

private theorem spinContorsion_eq_action (n a density : ℝ) (hn : 0 < n) (ha : 0 < a)
    (u v p q : ℂ) (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) (point : BasePoint) :
    contorsionOfCartanTorsion (diagonalCoframe n a)
      (cartanTorsionOfThreeForm (diagonalCoframe n a)
        (formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 point (spinField n a u v p q))) =
      homogeneousContorsion (a*density) := by
  have nonzero : (diagonalCoframe n a).det ≠ 0 := by
    rw [diagonalCoframe_det]
    exact mul_ne_zero (ne_of_gt hn) (pow_ne_zero _ (ne_of_gt ha))
  rw [← spinContorsion_generates n a density hn ha u v p q pv qu point,
    cartanTorsionOfThreeForm_leftInverse _ nonzero, contorsionOfCartanTorsion_leftInverse _ nonzero]

private theorem spinResponse_eq_field (current : StageNineHolonomicConfiguration) (point : BasePoint)
    (n a : ℝ) (u v p q : ℂ)
    (frame : current.coframe point = diagonalCoframe n a)
    (matter : current.matter point = spinPairMatter u v)
    (dual : current.conjugateMatter point = spinPairDual p q) :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource current point =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 point (spinField n a u v p q) := by
  funext pair triple
  change -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (restrictHolonomicConfigurationToIIPlus current) point)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) pair)) =
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
        (spinField n a u v p q)
        (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) pair))
  rw [formNativeLorentzMatterFirstCoefficient_restrictToIIPlus]
  unfold formNativeLorentzMatterFirstCoefficient matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation generatedVolumeDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart, spinField, homogeneousSpinField]
  rw [frame, matter, dual]

theorem movingContorsion_generated (current : StageNineHolonomicConfiguration) (point : BasePoint)
    (n a density : ℝ) (hn : 0 < n) (ha : 0 < a) (u v p q : ℂ)
    (frame : current.coframe point = diagonalCoframe n a)
    (matter : current.matter point = spinPairMatter u v)
    (dual : current.conjugateMatter point = spinPairDual p q)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) :
    diracDualFormNativeActionCartanContorsionAt positiveSmoothUnifiedSource current point =
      homogeneousContorsion (a*density) := by
  unfold diracDualFormNativeActionCartanContorsionAt diracDualFormNativeActionCartanTorsionAt
  rw [frame, spinResponse_eq_field current point n a u v p q frame matter dual]
  exact spinContorsion_eq_action n a density hn ha u v p q pv qu point

theorem dilution_square (a : ℝ) (ha : 0 < a) : dilution a ^ 2 = 1/a^3 := by
  rw [dilution, inv_pow, mul_pow, Real.sq_sqrt (le_of_lt ha), one_div]
  congr 1

private theorem phase_pair (amplitude density angle : ℝ) :
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

theorem Solution.contorsion_generated {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    diracDualFormNativeActionCartanContorsionAt positiveSmoothUnifiedSource flow.configuration point =
      homogeneousContorsion (contorsion (flow.pointState point)) := by
  let a := flow.pointState point 0
  let angle := flow.pointState point 6
  let density := spinScale * (dilution a)^2
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  have generated := movingContorsion_generated flow.configuration point
    (clock (flow.pointState point)) a density (clock_positive _ admissible) admissible.1
    ((dilution a : ℂ) * Complex.exp (Complex.I * (angle : ℂ)))
    ((dilution a : ℂ) * Complex.exp (-Complex.I * (angle : ℂ)))
    ((spinScale : ℂ) * (dilution a : ℂ) * Complex.exp (Complex.I * (angle : ℂ)))
    ((spinScale : ℂ) * (dilution a : ℂ) * Complex.exp (-Complex.I * (angle : ℂ)))
    rfl rfl rfl (phase_pair _ _ _) (by
      simpa only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg] using phase_pair (dilution a) spinScale (-angle))
  rw [generated]
  congr 1
  dsimp [density, contorsion, a]
  rw [dilution_square _ admissible.1]
  field_simp [ne_of_gt admissible.1]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
