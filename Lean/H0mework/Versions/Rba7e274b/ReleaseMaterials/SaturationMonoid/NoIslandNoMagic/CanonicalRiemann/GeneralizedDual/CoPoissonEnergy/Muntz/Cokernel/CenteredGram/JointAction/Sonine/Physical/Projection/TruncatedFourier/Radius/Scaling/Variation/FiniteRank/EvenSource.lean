import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.CenteredFinite
import H0mework.Versions.V2.Arithmetic.RieszForcing.SourceParity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

-- Reflection is transported by the actual radius chart, not supplied as a new field.
theorem chart_reflection (r : ℝ) (positive : 0<r) (x : BurnolRadiusIntervalL2 r) :
    burnolRadiusRechartEquiv positive (reflectRestricted r x) =
      reflectRestricted 1 (burnolRadiusRechartEquiv positive x) := by
  let chart := burnolRadiusRechartEquiv positive
  have source := (burnolRadiusScaleEquiv_measurePreserving positive).quasiMeasurePreserving.ae_eq
    (Measure.ae_smul_measure (Lp.coeFn_compMeasurePreserving x (negMeasurePreserving_restrict r))
      (ENNReal.ofReal r⁻¹))
  have negativeChart := (negMeasurePreserving_restrict 1).quasiMeasurePreserving.ae_eq
    (burnolRadiusRechart_coe positive x)
  apply Lp.ext
  filter_upwards [burnolRadiusRechart_coe positive (reflectRestricted r x),source,
    Lp.coeFn_compMeasurePreserving (chart x) (negMeasurePreserving_restrict 1),negativeChart] with y direct reflected unit negChart
  change (reflectRestricted r x : ℝ→ℂ) (r*y) = (x : ℝ→ℂ) (-(r*y)) at reflected
  change (reflectRestricted 1 (chart x) : ℝ→ℂ) y = (chart x : ℝ→ℂ) (-y) at unit
  change (chart x : ℝ→ℂ) (-y) = (Real.sqrt r : ℂ)*(x : ℝ→ℂ) (r*(-y)) at negChart
  change (burnolRadiusRechart positive (reflectRestricted r x) : ℝ→ℂ) y = (reflectRestricted 1 (chart x) : ℝ→ℂ) y
  rw [direct,unit,negChart,reflected]
  simp only [smul_eq_mul]
  congr 2
  ring

theorem original_source_Q (coordinate : BurnolCompletedMellinCoordinate) :
    Q (originalB coordinate) = originalB coordinate := by
  rw [originalB,← quarter_projection_chart]
  exact congrArg quarterChart (Submodule.starProjection_eq_self_iff.mpr (burnolRieszSingleFourierSource coordinate).property)

theorem original_source_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectRestricted 1 (originalB coordinate) = originalB coordinate := by
  rw [originalB,quarterChart,← chart_reflection,burnolRieszSingleFourierSource_reflection_fixed]

-- The concrete adjoint reads reflection; it is symmetric on the original even occurrence.
theorem radius_even_pair (r : ℝ) (left right : BurnolRadiusIntervalL2 r)
    (fixed : reflectRestricted r right = right) :
    inner ℂ (burnolRadiusTruncatedFourier r left) right =
      inner ℂ left (burnolRadiusTruncatedFourier r right) := by
  have reflected : reflectL2 (burnolRadiusZeroExtension r right) = burnolRadiusZeroExtension r right := by
    rw [burnolRadiusZeroExtension_reflect,fixed]
  have unitary := fourierL2.inner_map_map (burnolRadiusZeroExtension r left)
    (fourierL2 (burnolRadiusZeroExtension r right))
  rw [fourierL2_fourierL2,reflected] at unitary
  calc
    _ = inner ℂ (fourierL2 (burnolRadiusZeroExtension r left)) (burnolRadiusZeroExtension r right) :=
      (ContinuousLinearMap.adjoint_inner_right (burnolRadiusRestriction r) _ _).symm
    _ = inner ℂ (burnolRadiusZeroExtension r left) (fourierL2 (burnolRadiusZeroExtension r right)) := unitary
    _ = _ := ContinuousLinearMap.adjoint_inner_left (burnolRadiusRestriction r) _ _

theorem recharted_even_pair (r : ℝ) (positive : 0<r) (left right : H)
    (fixed : reflectRestricted 1 right = right) :
    inner ℂ (burnolRechartedTruncatedFourierOperator r left) right =
      inner ℂ left (burnolRechartedTruncatedFourierOperator r right) := by
  let A := burnolRadiusRechartEquiv positive
  have rightFixed : reflectRestricted r (A.symm right) = A.symm right := by
    apply A.injective
    rw [chart_reflection,A.apply_symm_apply,fixed]
  have source := radius_even_pair r (A.symm left) (A.symm right) rightFixed
  have actual := A.inner_map_map (burnolRadiusTruncatedFourier r (A.symm left)) (A.symm right)
  have other := A.inner_map_map (A.symm left) (burnolRadiusTruncatedFourier r (A.symm right))
  rw [A.apply_symm_apply] at actual other
  rw [source] at actual
  rw [← other] at actual
  rw [burnolRechartedTruncatedFourierOperator_of_pos positive]
  change inner ℂ (A (burnolRadiusTruncatedFourier r (A.symm left))) right =
    inner ℂ left (A (burnolRadiusTruncatedFourier r (A.symm right)))
  exact actual

theorem Q_reflection (x : H) :
    reflectRestricted 1 (Q x) = Q (reflectRestricted 1 x) := by
  rw [Q_read,Q_read,map_sub,map_smul]
  simp only [InnerProductSpace.rankOne_apply,map_smul]
  have unitFixed : reflectRestricted 1 e = e := reflectRestricted_intervalConstant 1
  rw [unitFixed]
  have pairing := (reflectRestricted 1).inner_map_map e x
  rw [unitFixed] at pairing
  rw [pairing]

theorem centered_even_pair (r : ℝ) (positive : 0<r) (left right : H)
    (fixed : reflectRestricted 1 right = right) :
    inner ℂ (centeredOperator r left) right = inner ℂ left (centeredOperator r right) := by
  unfold centeredOperator
  simp only [ContinuousLinearMap.comp_apply]
  have projectionPair (x y : H) : inner ℂ (Q x) y = inner ℂ x (Q y) := Q_symmetric x y
  rw [projectionPair]
  rw [recharted_even_pair r positive (Q left) (Q right) (by rw [Q_reflection,fixed])]
  exact projectionPair _ _

theorem centered_source_even (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) (positive : 0<r) :
    reflectRestricted 1 (centeredOperator r (originalB coordinate)) = centeredOperator r (originalB coordinate) := by
  have chartFixed := original_source_even coordinate
  let A := burnolRadiusRechartEquiv positive
  have rightFixed : reflectRestricted r (A.symm (originalB coordinate)) = A.symm (originalB coordinate) := by
    apply A.injective
    rw [chart_reflection,A.apply_symm_apply,chartFixed]
  have radiusFixed : reflectRestricted r (burnolRadiusTruncatedFourier r (A.symm (originalB coordinate))) =
      burnolRadiusTruncatedFourier r (A.symm (originalB coordinate)) := by
    change reflectRestricted r (restrictToInterval r (fourierL2 (burnolRadiusZeroExtension r (A.symm (originalB coordinate))))) = _
    rw [← restrictToInterval_reflectL2,← fourierL2_reflectL2_commute,burnolRadiusZeroExtension_reflect,rightFixed]
    rfl
  unfold centeredOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [original_source_Q, Q_reflection]
  rw [burnolRechartedTruncatedFourierOperator_of_pos positive]
  change Q (reflectRestricted 1 (A (burnolRadiusTruncatedFourier r (A.symm (originalB coordinate))))) = _
  rw [← chart_reflection,radiusFixed]
  rfl

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
