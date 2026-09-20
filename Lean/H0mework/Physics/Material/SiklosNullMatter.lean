import H0mework.Physics.Material.NullSource
import H0mework.Physics.PlaneWave.Coframe

/-! Null Clifford and scalar contractions on the exact Siklos coframe.
The wave shear never enters the source null direction, and the full P286
amplitude is allowed to vary in its Lie carrier. -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace SaturationMonoid.PhysicsCore.Stage9C.Material

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open Stage9C.Dynamics.PlaneWave
open StageNineCoframeVariation
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRestriction

noncomputable section

def sourceNullCovector : LorentzianIndex → ℝ := ![1, 0, 0, -1]

def sourceNullScalarDerivative (value : ScalarCoordinateCarrier) :
    LorentzianIndex → ScalarCoordinateCarrier :=
  fun direction => sourceNullCovector direction • value

theorem siklosCoframeScale_nullClifford
    (q H : ℝ) (hq : q ≠ 0) :
    inverseCoframeDiracGamma { coframe := siklosCoframeScale q H, derivative := 0 } 0 -
      inverseCoframeDiracGamma { coframe := siklosCoframeScale q H, derivative := 0 } 3 =
        ((q⁻¹ : ℝ) : ℂ) • sourceNullClifford := by
  unfold inverseCoframeDiracGamma
  rw [siklosCoframeScale_inv q H hq]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [adsCoframeScale, nullShear, sourceNullClifford, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem siklosCoframeScale_nullMatter_zero
    (q H : ℝ) (hq : q ≠ 0) :
    diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := siklosCoframeScale q H, derivative := 0 } 0 -
        inverseCoframeDiracGamma { coframe := siklosCoframeScale q H, derivative := 0 } 3)
      diracSpinTwoMatterProbe = 0 := by
  rw [siklosCoframeScale_nullClifford q H hq,
    StageNineCoframeLocalDifferentiability.coframeDiracMatrixMatterAction_smul_matrix,
    sourceNullClifford_matter_zero, smul_zero]

private theorem siklosCoframeScale_metric_inv (q H : ℝ) (hq : q ≠ 0) :
    (lorentzianMetricOfCoframe (siklosCoframeScale q H))⁻¹ =
      nullShear (-H) * adsCoframeScale q⁻¹ * minkowskiInternalMetric *
        (nullShear (-H) * adsCoframeScale q⁻¹).transpose := by
  have metricInverse : minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
    apply Matrix.inv_eq_left_inv
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [minkowskiInternalMetric, Matrix.mul_apply,
        Fin.sum_univ_four]
  unfold lorentzianMetricOfCoframe
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, metricInverse,
    ← Matrix.transpose_nonsing_inv, siklosCoframeScale_inv q H hq]
  simp only [Matrix.mul_assoc]

theorem siklosCoframeScale_inverseMetric_nullContraction
    (q H : ℝ) (hq : q ≠ 0) (direction : LorentzianIndex) :
    ∑ other : LorentzianIndex,
      (lorentzianMetricOfCoframe (siklosCoframeScale q H))⁻¹ direction other *
        sourceNullCovector other =
      if direction = 0 ∨ direction = 3 then -(q⁻¹ ^ 2) else 0 := by
  rw [siklosCoframeScale_metric_inv q H hq]
  fin_cases direction <;>
    simp [nullShear, adsCoframeScale, minkowskiInternalMetric,
      sourceNullCovector, Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_four] <;> ring

theorem siklosCoframeScale_nullScalarKinetic_zero
    (source : SmoothUnifiedSource) (point : BasePoint)
    (q H : ℝ) (hq : q ≠ 0) (field : StageNineContinuumPointField)
    (value : ScalarCoordinateCarrier) :
    generatedScalarKineticDensity source 0 point
      { field with
        coframe := siklosCoframeScale q H
        scalarCovariantDerivative := sourceNullScalarDerivative value } = 0 := by
  unfold generatedScalarKineticDensity
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    sourceNullScalarDerivative]
  simp_rw [scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  rw [siklosCoframeScale_metric_inv q H hq]
  simp [sourceNullCovector, nullShear, adsCoframeScale, minkowskiInternalMetric,
    Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_four]
  ring

theorem siklosCoframeScale_nullScalarFirstVariation_zero
    (source : SmoothUnifiedSource) (point : BasePoint)
    (q H : ℝ) (hq : q ≠ 0) (field : StageNineContinuumPointField)
    (value variation : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      { field with
        coframe := siklosCoframeScale q H
        scalarCovariantDerivative := sourceNullScalarDerivative value }
      (sourceNullScalarDerivative variation) = 0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    sourceNullScalarDerivative]
  simp_rw [scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  rw [siklosCoframeScale_metric_inv q H hq]
  simp [sourceNullCovector, nullShear, adsCoframeScale, minkowskiInternalMetric,
    Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_four]
  ring

theorem siklosCoframeScale_nullScalarMomentum_coefficient
    (source : SmoothUnifiedSource) (point : BasePoint)
    (q H : ℝ) (hq : q ≠ 0) (field : StageNineContinuumPointField)
    (value variation : ScalarCoordinateCarrier) (direction : LorentzianIndex) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      { field with
        coframe := siklosCoframeScale q H
        scalarCovariantDerivative := sourceNullScalarDerivative value }
      (scalarVariationDifferentialDirection variation direction) =
      if direction = 0 ∨ direction = 3 then
        -(q⁻¹ ^ 2) * scalarCoordinatePairingRe variation value else 0 := by
  have pairSwap : scalarCoordinatePairingRe value variation =
      scalarCoordinatePairingRe variation value := by
    unfold scalarCoordinatePairingRe
    apply Finset.sum_congr rfl
    intro index _
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have leftZero : scalarCoordinatePairingRe 0 value = 0 := by
    simp [scalarCoordinatePairingRe]
  have rightZero : scalarCoordinatePairingRe value 0 = 0 := by
    simp [scalarCoordinatePairingRe]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    sourceNullScalarDerivative]
  simp_rw [scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  rw [siklosCoframeScale_metric_inv q H hq]
  fin_cases direction <;>
    simp +decide [scalarVariationDifferentialDirection, sourceNullCovector,
      nullShear, adsCoframeScale, minkowskiInternalMetric, Matrix.mul_apply,
      Matrix.vecMul, Fin.sum_univ_four]
  all_goals
    simp only [pairSwap, leftZero, rightZero]
    ring

end
end SaturationMonoid.PhysicsCore.Stage9C.Material
