import H0mework.Physics.Homogeneous.Cartan
import H0mework.Physics.SpinPair.Spinor
import H0mework.Physics.PlaneWave.NullSpin

/-! The original W13 action generates the isotropic Cartan connection from the source spin/color pair. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineHolonomicField StageNineCoframeFirstJet
open StageNineLorentzConnectionVariation
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineEnrichedProofFreeSource StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeLorentzGeometricFirstVariation StageNineTopologicalLorentzThreeFormDuality
open StageNineMatterCovariantDerivativeAffine StageNineP286GaugeConnectionVariationDensity
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineMatterVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineCartanAffineConnectionActualization StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormEquiv StageNineCartanTorsionThreeFormCoordinates
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open Material.SpinPair

noncomputable section

def homogeneousSpinField (lapse : ℝ) (u v p q : ℂ) : StageNineContinuumPointField where
  coframe := homogeneousCoframe lapse
  gravityCurvature := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeCurvature := 0
  gaugeAuxiliary := 0
  scalar := 0
  scalarCovariantDerivative := 0
  matter := spinPairMatter u v
  matterCovariantDerivative := 0
  conjugateMatter := spinPairDual p q

private def homogeneousSpinCoefficient (density : ℝ) (μ : LorentzianIndex) (pair : Fin 6) : ℝ :=
  if (μ = 1 ∧ pair = 3) ∨ (μ = 2 ∧ pair = 4) ∨ (μ = 3 ∧ pair = 5) then -2*density else 0

private theorem homogeneousSpin_triple_read
    (u v p q : ℂ) (density : ℝ)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ))
    (μ : LorentzianIndex) (pair : Fin 6) :
    (Complex.I * (2 : ℂ)⁻¹ * spinPairDual p q
      (diracMatrixMatterAction
        (diracGamma μ * (diracGamma (pairFirst pair) * diracGamma (pairSecond pair)))
        (spinPairMatter u v))).re = homogeneousSpinCoefficient density μ pair := by
  rw [spinPairDual_diracMatrix, pv, qu]
  fin_cases μ <;> fin_cases pair <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, pairFirst, pairSecond,
      homogeneousSpinCoefficient, Complex.mul_re, Complex.mul_im] <;> ring

theorem homogeneousSpinField_coefficient
    (lapse density : ℝ) (positive : 0 < lapse) (u v p q : ℂ)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ))
    (point : BasePoint) (μ : LorentzianIndex) (pair : Fin 6) :
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
        (homogeneousSpinField lapse u v p q) (loweredLorentzBivectorOneFormCoordinate μ pair) =
      lapse * homogeneousSpinCoefficient density μ pair := by
  unfold formNativeLorentzMatterFirstCoefficient matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
  simp only [matterDualFrameRelative_chartZero, matterDerivativeFrameRelative_zeroChart,
    homogeneousSpinField, PlaneWave.spinLift_coordinate]
  rw [Finset.sum_eq_single μ]
  · simp only [ite_true, map_smul]
    rw [PlaneWave.matrixAction_comp]
    have gamma : inverseCoframeDiracGamma
        { coframe := homogeneousCoframe lapse, derivative := 0 } μ =
        (if μ = 0 then lapse⁻¹ else 1 : ℝ) • diracGamma μ := by
      unfold inverseCoframeDiracGamma
      rw [homogeneousCoframe_inv lapse (ne_of_gt positive)]
      fin_cases μ <;> simp [homogeneousCoframe, Fin.sum_univ_four]
    rw [gamma]
    simp only [Matrix.smul_mul]
    unfold generatedVolumeDensity
    rw [homogeneousCoframe_det, abs_of_pos positive]
    simp only [Matrix.mul_smul, diracMatrixMatterAction_real_smul_matrix_local,
      StageNineCoframeLocalDifferentiability.coframeDiracMatrixMatterAction_smul_matrix]
    simp only [(spinPairDual p q).map_smul_of_tower, smul_eq_mul]
    have scalarRead (coefficient : ℝ) (value : ℂ) :
        (Complex.I * (coefficient • ((2 : ℂ)⁻¹ * value))).re =
          coefficient * (Complex.I * (2 : ℂ)⁻¹ * value).re := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [scalarRead, homogeneousSpin_triple_read u v p q density pv qu]
    by_cases temporal : μ = 0
    · subst μ
      simp [homogeneousSpinCoefficient]
    · simp [temporal]
  · intro ν _ different
    simp [different]
  · simp

private def homogeneousTorsion (density : ℝ) : PointwiseCartanTorsionTwoForm :=
  ⟨!![0,0,0,0;0,0,0,0;0,0,0,0;0,-2*density,0,0;0,0,-2*density,0;0,0,0,-2*density]⟩

private theorem homogeneousContorsion_torsion (lapse density : ℝ) :
    actualCartanTorsionIncrementTwoForm (homogeneousCoframe lapse)
      (homogeneousContorsion density) = homogeneousTorsion density := by
  ext pair internal
  simp only [actualCartanTorsionIncrementTwoForm, actualPointwiseCartanTorsionTwoForm,
    pointwiseCartanTorsion, pointwiseCoframeCovariantDerivative, coframeConnectionAction,
    Pi.zero_apply, zero_add]
  simp only [homogeneousCoframe, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases pair <;> fin_cases internal <;>
    simp [homogeneousContorsion, homogeneousTorsion, lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] <;> ring

theorem homogeneousContorsion_generates_spin
    (lapse density : ℝ) (positive : 0 < lapse) (u v p q : ℂ)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) (point : BasePoint) :
    cartanTorsionThreeForm (homogeneousCoframe lapse)
      (cartanTorsionOfContorsion (homogeneousCoframe lapse) (homogeneousContorsion density)) =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 point
        (homogeneousSpinField lapse u v p q) := by
  rw [← actualCartanTorsionIncrementTwoForm_eq_factored (homogeneousCoframe lapse)
    (homogeneousCoframe_nondegenerate lapse positive), homogeneousContorsion_torsion]
  funext pair triple
  change _ = -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
      (homogeneousSpinField lapse u v p q)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) pair))
  rw [homogeneousSpinField_coefficient lapse density positive u v p q pv qu point]
  fin_cases pair <;> fin_cases triple <;>
    simp [cartanTorsionThreeForm, cartanTorsionCoframeWedgeThreeForm,
      rawPointwiseCartanTorsion, orderedCartanTorsionComponent,
      internalBivectorDualThreeForm, torsionCoframeWedgeThreeForm,
      homogeneousTorsion, homogeneousSpinCoefficient, homogeneousCoframe,
      orientedLorentzBivectorBasisCoefficient, lorentzianCoframeHodge,
      pairFirst, pairSecond, threeFormFirst, threeFormSecond, threeFormThird,
      oneWedgeThreeSign, missingTripleOfOneForm, Fin.sum_univ_six] <;> ring

theorem homogeneousContorsion_eq_action
    (lapse density : ℝ) (positive : 0 < lapse) (u v p q : ℂ)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) (point : BasePoint) :
    contorsionOfCartanTorsion (homogeneousCoframe lapse)
      (cartanTorsionOfThreeForm (homogeneousCoframe lapse)
        (formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 point
          (homogeneousSpinField lapse u v p q))) = homogeneousContorsion density := by
  rw [← homogeneousContorsion_generates_spin lapse density positive u v p q pv qu point,
    cartanTorsionOfThreeForm_leftInverse _ (homogeneousCoframe_nondegenerate lapse positive),
    contorsionOfCartanTorsion_leftInverse _ (homogeneousCoframe_nondegenerate lapse positive)]

theorem homogeneousContorsion_generated
    (current : StageNineHolonomicConfiguration) (point : BasePoint)
    (lapse density : ℝ) (positive : 0 < lapse) (u v p q : ℂ)
    (coframe : current.coframe point = homogeneousCoframe lapse)
    (matter : current.matter point = spinPairMatter u v)
    (dual : current.conjugateMatter point = spinPairDual p q)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) :
    diracDualFormNativeActionCartanContorsionAt positiveSmoothUnifiedSource current point =
      homogeneousContorsion density := by
  let reference : StageNineHolonomicConfiguration :=
    { current with coframe := fun _ => homogeneousCoframe lapse
                   matter := fun _ => spinPairMatter u v
                   conjugateMatter := fun _ => spinPairDual p q }
  have response : diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource current point =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource reference 0 :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
      positiveSmoothUnifiedSource current reference point 0 coframe matter dual
  unfold diracDualFormNativeActionCartanContorsionAt diracDualFormNativeActionCartanTorsionAt
  rw [coframe, response]
  exact homogeneousContorsion_eq_action lapse density positive u v p q pv qu 0

theorem homogeneousConnection_generated
    (current : StageNineHolonomicConfiguration) (point : BasePoint)
    (lapse density : ℝ) (positive : 0 < lapse) (u v p q : ℂ)
    (coframe : current.coframe = fun _ => homogeneousCoframe lapse)
    (matter : current.matter point = spinPairMatter u v)
    (dual : current.conjugateMatter point = spinPairDual p q)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource current point =
      homogeneousConnection density := by
  unfold diracDualFormNativeActionCartanConnectionAt cartanAffineSpinConnection
  rw [homogeneousContorsion_generated current point lapse density positive u v p q
    (congrFun coframe point) matter dual pv qu, coframe, homogeneousCoframe_generatedLC]
  simp [homogeneousConnection]

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous
