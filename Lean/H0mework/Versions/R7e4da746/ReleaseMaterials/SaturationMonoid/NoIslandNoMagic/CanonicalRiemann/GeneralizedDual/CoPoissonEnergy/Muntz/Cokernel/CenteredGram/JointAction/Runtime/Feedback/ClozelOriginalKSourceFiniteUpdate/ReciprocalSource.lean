import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.ContactAction
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSourceGreen.Correction
import H0mework.Versions.R7e4da746.Arithmetic.RiemannNativeCurrent.WeylPairing

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate
open Complex MeasureTheory FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalKFixedBoundarySourceFibre OriginalPrimitiveRankBalance
open scoped InnerProductSpace
noncomputable section

private theorem reciprocal_rate_positive (c : BurnolCompletedMellinCoordinate) :
    0 < (sourceRate c).re := by
  simp only [sourceRate, Complex.sub_re, Complex.star_def, Complex.conj_re]
  norm_num
  linarith [c.rightHalf]

/-- The reciprocal source reads only the full Fourier input and the actual conjugate resolvent. -/
def sourceReciprocity (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  -fourierL2.toContinuousLinearEquiv.toContinuousLinearMap -
    sourceRate c • ((burnolDirectRightResolventCLM (conjugateCoordinate c)).comp
      fourierL2.toContinuousLinearEquiv.toContinuousLinearMap)

theorem sourceReciprocity_apply (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceReciprocity c value = -fourierL2 value -
      sourceRate c • sourceResolvent c (fourierL2 value) := rfl

theorem sourceReciprocity_euler (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    GapEuler.euler (sourceReciprocity c value : TemperedDistribution ℝ ℂ) +
      sourceRate c • (sourceReciprocity c value : TemperedDistribution ℝ ℂ) =
    FourierTransform.fourier (GapEuler.euler (value : TemperedDistribution ℝ ℂ) +
      sourceRate c • (value : TemperedDistribution ℝ ℂ)) := by
  have inverse := sourceResolvent_euler c (fourierL2 value)
  have native : FourierTransform.fourier (value : TemperedDistribution ℝ ℂ) =
      (fourierL2 value : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq value
  have reverse : GapEuler.euler (fourierL2 value : TemperedDistribution ℝ ℂ) =
      -FourierTransform.fourier (GapEuler.euler (value : TemperedDistribution ℝ ℂ)) := by
    rw [←native, GapEuler.euler_fourier]
  rw [sourceReciprocity_apply]
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (-fourierL2 value - sourceRate c • sourceResolvent c (fourierL2 value))) +
    sourceRate c • Lp.toTemperedDistributionCLM ℂ volume 2
      (-fourierL2 value - sourceRate c • sourceResolvent c (fourierL2 value)) =
    (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) _
  simp only [map_sub, map_neg, map_smul, Lp.toTemperedDistributionCLM_apply, map_add]
  simp only [FourierTransform.fourierCLM_apply]
  rw [reverse, native]
  linear_combination (norm := module) -(sourceRate c) • inverse

/-- The original complete second column is generated from the first, including its contact. -/
theorem sourceY1_reciprocal_source (c : BurnolCompletedMellinCoordinate) :
    sourceY1 c = sourceReciprocity c (sourceY0 c) := by
  have generated := sourceReciprocity_euler c (sourceY0 c)
  rw [sourceY0_euler] at generated
  have original := sourceY1_euler c
  have homogeneous : GapEuler.euler
      ((sourceY1 c - sourceReciprocity c (sourceY0 c) : BurnolL2) : TemperedDistribution ℝ ℂ) +
    sourceRate c •
      ((sourceY1 c - sourceReciprocity c (sourceY0 c) : BurnolL2) : TemperedDistribution ℝ ℂ) = 0 := by
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (sourceY1 c - sourceReciprocity c (sourceY0 c))) +
      sourceRate c • Lp.toTemperedDistributionCLM ℂ volume 2
        (sourceY1 c - sourceReciprocity c (sourceY0 c)) = 0
    simp only [map_sub, Lp.toTemperedDistributionCLM_apply]
    linear_combination (norm := module) original - generated
  exact sub_eq_zero.mp (homogeneous_L2_unique _ (reciprocal_rate_positive c) _ homogeneous)

theorem sourceReciprocity_dilation (c : BurnolCompletedMellinCoordinate) (h : ℝ) (value : BurnolL2) :
    sourceReciprocity c (burnolMultiplicativeDilation h value) =
      burnolMultiplicativeDilation (-h) (sourceReciprocity c value) := by
  rw [sourceReciprocity_apply, sourceReciprocity_apply, fourierL2_burnolMultiplicativeDilation]
  change -burnolMultiplicativeDilation (-h) (fourierL2 value) -
    sourceRate c • burnolDirectRightResolvent (star c.value/2)
      (burnolMultiplicativeDilation (-h) (fourierL2 value)) = _
  rw [burnolDirectRightResolvent_dilation, map_sub, map_neg, map_smul]
  rfl

theorem sourceReciprocity_boundary (c : BurnolCompletedMellinCoordinate) (h : ℝ) (value : BurnolL2) :
    sourceReciprocity c (finiteBoundaryAction c h value) =
      finiteBoundaryAction c h (sourceReciprocity c value) := by
  simp only [finiteBoundaryAction, map_sub, map_smul, map_add, sourceReciprocity_dilation, neg_neg]
  rw [add_comm (burnolMultiplicativeDilation (-h) _) (burnolMultiplicativeDilation h _)]

theorem second_contact_boundary_reciprocal (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    contactSourceBoundaryColumn c h 1 = sourceReciprocity c (contactSourceBoundaryColumn c h 0) := by
  rw [contact_source_column_actual, contact_source_column_actual,
    ←source_columns_boundary_action, ←source_columns_boundary_action]
  change finiteBoundaryAction c h (sourceY1 c) = sourceReciprocity c (finiteBoundaryAction c h (sourceY0 c))
  rw [sourceY1_reciprocal_source, sourceReciprocity_boundary]

/-- The first source word and its generated reciprocal replace the two independent columns. -/
def reciprocalSourceBoundary (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  Kernel.A c • contactSourceBoundaryColumn c h 0 +
    Kernel.beta c • sourceReciprocity c (contactSourceBoundaryColumn c h 0)

theorem reciprocal_source_word_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    reciprocalSourceBoundary c h = contactSourceBoundary c h := by
  simp only [contactSourceBoundary, Fin.sum_univ_two, sourceCoefficients,
    Matrix.cons_val_zero, Matrix.cons_val_one, reciprocalSourceBoundary,
    second_contact_boundary_reciprocal]

theorem original_fixedResidual_reciprocal_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    burnolPaFixedShiftResidual c zero =
      -inner ℂ (generatedK c) (reciprocalSourceBoundary c (Real.log stageZeroSonineQ)) := by
  rw [reciprocal_source_word_actual]
  exact original_fixedResidual_contact_source c zero

private def reciprocalPaFourier (p : burnolCompactCoPoissonClosedRange) :
    burnolCompactCoPoissonClosedRange :=
  ⟨evenFaceFourierEquiv burnolUnscaledCommonGapRadius (p : BurnolPaAmbientCarrier),
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange p.property⟩

def reciprocalPaSource (c : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange) : BurnolPaAmbientCarrier :=
  -(reciprocalPaFourier p : BurnolPaAmbientCarrier) -
    sourceRate c • burnolPaSourceCorrection (conjugateCoordinate c) (reciprocalPaFourier p)

theorem reciprocalPaSource_mem (c : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange) : reciprocalPaSource c p ∈ burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem
    (burnolCompactCoPoissonClosedRange.toSubmodule.neg_mem (reciprocalPaFourier p).property)
    (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _
      (burnolPaSourceCorrection_mem (conjugateCoordinate c) (reciprocalPaFourier p)))

/-- The Pa correction keeps the actual conjugate unit and its complete original source coefficient. -/
theorem reciprocal_pa_source_cocycle (c : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange) :
    sourceReciprocity c (p : BurnolL2) = (reciprocalPaSource c p : BurnolL2) -
      (sourceRate c * burnolPaResolventSourceCoefficient (conjugateCoordinate c)
        (reciprocalPaFourier p : BurnolPaAmbientCarrier)) • burnolUnitTailResponse (conjugateCoordinate c) 4 := by
  rw [sourceReciprocity_apply]
  change -fourierL2 (p : BurnolL2) - sourceRate c •
      sourceResolvent c (fourierL2 (p : BurnolL2)) =
    (-fourierL2 (p : BurnolL2) - sourceRate c •
      (sourceResolvent c (fourierL2 (p : BurnolL2)) -
        burnolPaResolventSourceCoefficient (conjugateCoordinate c)
          (reciprocalPaFourier p : BurnolPaAmbientCarrier) • burnolUnitTailResponse (conjugateCoordinate c) 4)) - _
  module

theorem reciprocal_pa_originalK_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (p : burnolCompactCoPoissonClosedRange) :
    inner ℂ (generatedK c) (sourceReciprocity c (p : BurnolL2)) =
      -(sourceRate c * burnolPaResolventSourceCoefficient (conjugateCoordinate c)
        (reciprocalPaFourier p : BurnolPaAmbientCarrier)) *
          inner ℂ (generatedK c) (burnolUnitTailResponse (conjugateCoordinate c) 4) := by
  rw [reciprocal_pa_source_cocycle, inner_sub_right, inner_smul_right]
  have killed : inner ℂ (generatedK c) (reciprocalPaSource c p : BurnolL2) = 0 := by
    rw [generatedK_eq_original]
    exact (Submodule.mem_orthogonal' _ _).mp
      (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero)
        (reciprocalPaSource c p) (reciprocalPaSource_mem c p)
  rw [killed]
  ring

end
end OriginalKSourceFiniteUpdate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
