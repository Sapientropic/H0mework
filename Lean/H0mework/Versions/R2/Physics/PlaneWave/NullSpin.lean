import H0mework.Versions.R2.Physics.Material.NullCartanDirac
import H0mework.Versions.R2.Physics.Material.SiklosActual
import H0mework.Physics.PlaneWave.AdSGeometry
import H0mework.Physics.CartanAction.CartanConnectionActualization

/-! The original null matter source generates its exact Cartan contorsion.
The finite table is identified by the physical W13 response and both existing
Cartan inverses before being consumed on the shared AdS actual. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave

open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineFormNativeMatterSpinThreeForm StageNineLorentzConnectionVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineTopologicalLorentzThreeFormDuality StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeConnectionVariationDensity
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineMatterVariation
open SU7ExteriorMatterGaugeCovariantJet SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv StageNineCartanTorsionThreeFormEquiv
open StageNineCartanTorsionThreeFormCoordinates StageNineResidualLinearPlebanskiTorsionReduction
open scoped Matrix

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def nullSpinField (q s : ℝ) : StageNineContinuumPointField where
  coframe := adsCoframeScale q
  gravityCurvature := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeCurvature := 0
  gaugeAuxiliary := 0
  scalar := 0
  scalarCovariantDerivative := 0
  matter := (s : ℂ) • diracSpinTwoMatterProbe
  matterCovariantDerivative := 0
  conjugateMatter := (s : ℂ) • diracSpinZeroMatterCoordinate

theorem sourceSpinProbe_matrixRead (matrix : DiracMatrix) :
    diracSpinZeroMatterCoordinate (diracMatrixMatterAction matrix diracSpinTwoMatterProbe) =
      matrix 0 2 := by
  simp [diracSpinZeroMatterCoordinate, diracMatrixMatterAction, diracSpinTwoMatterProbe,
    hyperchargeDegreeTwoMatterCoordinate, p286HyperchargeMatterProbe, Fin.sum_univ_four]

theorem matrixAction_comp (first second : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction first (diracMatrixMatterAction second matter) =
      diracMatrixMatterAction (first * second) matter := by
  rw [diracMatrixMatterAction_mul, LinearMap.comp_apply]

theorem spinLift_coordinate (μ ν : LorentzianIndex) (pair : Fin 6) :
    diracSpinConnectionLift
        (lorentzSkewConnectionOfBivectorOneForm
          (loweredLorentzBivectorOneFormCoordinate μ pair)) ν =
      if ν = μ then (2 : ℂ)⁻¹ •
        (diracGamma (pairFirst pair) * diracGamma (pairSecond pair)) else 0 := by
  simp only [diracSpinConnectionLift, loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  unfold loweredLorentzBivectorOneFormCoordinate
  by_cases h : ν = μ
  · subst ν
    rw [Finset.sum_eq_single pair]
    · simp [lorentzBivectorFirst, lorentzBivectorSecond, pairFirst, pairSecond]
    · intro p _ hp
      simp [hp]
    · simp
  · simp [h]

def nullSpinCoefficientTable : LorentzianIndex → Fin 6 → ℝ :=
  !![0,0,0,0,0,-1/2; 0,1/2,0,-1/2,0,0; -1/2,0,0,0,-1/2,0; 0,0,0,0,0,-1/2]

theorem spinTriple_matrixRead (μ : LorentzianIndex) (pair : Fin 6) :
    (Complex.I * (2 : ℂ)⁻¹ *
      (diracGamma μ * (diracGamma (pairFirst pair) * diracGamma (pairSecond pair))) 0 2).re =
      nullSpinCoefficientTable μ pair := by
  fin_cases μ <;> fin_cases pair <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, pairFirst, pairSecond, nullSpinCoefficientTable] <;> norm_num

theorem nullSpinField_coefficient (q s : ℝ) (hq : 0 < q)
    (μ : LorentzianIndex) (pair : Fin 6) :
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 0 (nullSpinField q s)
        (loweredLorentzBivectorOneFormCoordinate μ pair) =
      q^3 * s^2 * (if μ = 2 then 1 else q⁻¹) * nullSpinCoefficientTable μ pair := by
  unfold formNativeLorentzMatterFirstCoefficient matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
  simp only [matterDualFrameRelative_chartZero, matterDerivativeFrameRelative_zeroChart,
    nullSpinField, spinLift_coordinate]
  rw [Finset.sum_eq_single μ]
  · simp only [ite_true, map_smul, LinearMap.smul_apply, smul_smul]
    rw [matrixAction_comp]
    have gamma : inverseCoframeDiracGamma
        { coframe := adsCoframeScale q, derivative := 0 } μ =
        (if μ = 2 then 1 else q⁻¹ : ℝ) • diracGamma μ := by
      unfold inverseCoframeDiracGamma
      rw [adsCoframeScale_inv q (ne_of_gt hq)]
      fin_cases μ <;> simp [adsCoframeScale, Fin.sum_univ_four]
    rw [gamma]
    simp only [Matrix.smul_mul]
    rw [sourceSpinProbe_matrixRead]
    unfold generatedVolumeDensity
    rw [adsCoframeScale_det, abs_of_pos (pow_pos hq 3)]
    rw [← spinTriple_matrixRead μ pair]
    by_cases hm : μ = 2 <;>
      simp [hm, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring
  · intro ν _ hν
    simp [hν]
  · simp

private def sourceNullTorsionTable (q density : ℝ) : PointwiseCartanTorsionTwoForm :=
  ⟨!![0,0,q^2*density/2,0; 0,-q*density/2,0,0; 0,0,0,0;
      0,-q*density/2,0,0; 0,0,-q^2*density/2,0; -q*density/2,0,0,-q*density/2]⟩

private theorem sourceNullContorsion_torsion (q density : ℝ) :
    actualCartanTorsionIncrementTwoForm (adsCoframeScale q)
      (Material.sourceNullContorsion q density) = sourceNullTorsionTable q density := by
  ext pair internal
  simp only [actualCartanTorsionIncrementTwoForm, actualPointwiseCartanTorsionTwoForm,
    pointwiseCartanTorsion, pointwiseCoframeCovariantDerivative, coframeConnectionAction,
    Pi.zero_apply, zero_add]
  simp only [adsCoframeScale, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases pair <;> fin_cases internal <;>
    simp [Material.sourceNullContorsion, lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
      sourceNullTorsionTable, pairFirst, pairSecond,
      minkowskiInternalSign, Fin.sum_univ_six] <;> ring

theorem sourceNullContorsion_generates_spin (q s : ℝ) (hq : 0 < q) :
    cartanTorsionThreeForm (adsCoframeScale q)
      (cartanTorsionOfContorsion (adsCoframeScale q) (Material.sourceNullContorsion q (s^2))) =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0 (nullSpinField q s) := by
  rw [← actualCartanTorsionIncrementTwoForm_eq_factored (adsCoframeScale q)
    (by rw [adsCoframeScale_det]; exact pow_ne_zero 3 (ne_of_gt hq))]
  rw [sourceNullContorsion_torsion]
  funext pair triple
  change _ = -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 0 (nullSpinField q s)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) pair))
  rw [nullSpinField_coefficient q s hq]
  fin_cases pair <;> fin_cases triple <;>
    simp [cartanTorsionThreeForm, cartanTorsionCoframeWedgeThreeForm,
      rawPointwiseCartanTorsion, orderedCartanTorsionComponent,
      internalBivectorDualThreeForm, torsionCoframeWedgeThreeForm,
      sourceNullTorsionTable, orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, adsCoframeScale, pairFirst, pairSecond, threeFormFirst,
      threeFormSecond, threeFormThird, oneWedgeThreeSign, missingTripleOfOneForm,
      nullSpinCoefficientTable, Fin.sum_univ_six] <;>
    field_simp

theorem sourceNullContorsion_eq_action (q s : ℝ) (hq : 0 < q) :
    contorsionOfCartanTorsion (adsCoframeScale q)
      (cartanTorsionOfThreeForm (adsCoframeScale q)
        (formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0 (nullSpinField q s))) =
      Material.sourceNullContorsion q (s^2) := by
  have nondegenerate : (adsCoframeScale q).det ≠ 0 := by
    rw [adsCoframeScale_det]
    exact pow_ne_zero 3 (ne_of_gt hq)
  rw [← sourceNullContorsion_generates_spin q s hq,
    cartanTorsionOfThreeForm_leftInverse _ nondegenerate,
    contorsionOfCartanTorsion_leftInverse _ nondegenerate]

private def nullSpinConfiguration (q s : ℝ) : StageNineHolonomicConfiguration :=
  { Material.firstAssemblyCartanActual with
    coframe := fun _ => adsCoframeScale q
    matter := fun _ => (s : ℂ) • diracSpinTwoMatterProbe
    conjugateMatter := fun _ => (s : ℂ) • diracSpinZeroMatterCoordinate }

theorem adsNullActual_contorsion
    (amplitude : ℝ → P286CoordinateCarrier) (point : BasePoint) :
    diracDualFormNativeActionCartanContorsionAt positiveSmoothUnifiedSource
      (Material.siklosActual (fun _ => 0) amplitude) point =
      Material.sourceNullContorsion (adsScale point) (Material.siklosMatterWeight (point 2)^2) := by
  let actual := Material.siklosActual (fun _ => 0) amplitude
  let q := adsScale point
  let s := Material.siklosMatterWeight (point 2)
  have coframe : actual.coframe point = adsCoframeScale q := by
    rw [Material.siklosActual_coframe]
    simp [siklosCoframe, siklosCoframeScale, q]
  have response : diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource actual point =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource (nullSpinConfiguration q s) 0 := by
    exact diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
      positiveSmoothUnifiedSource actual (nullSpinConfiguration q s) point 0 coframe
      (Material.siklosActual_matter _ _ _) (Material.siklosActual_conjugateMatter _ _ _)
  unfold diracDualFormNativeActionCartanContorsionAt diracDualFormNativeActionCartanTorsionAt
  rw [show (Material.siklosActual (fun _ => 0) amplitude).coframe point = adsCoframeScale q from coframe,
    response]
  exact sourceNullContorsion_eq_action q s (Real.exp_pos _)

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave
