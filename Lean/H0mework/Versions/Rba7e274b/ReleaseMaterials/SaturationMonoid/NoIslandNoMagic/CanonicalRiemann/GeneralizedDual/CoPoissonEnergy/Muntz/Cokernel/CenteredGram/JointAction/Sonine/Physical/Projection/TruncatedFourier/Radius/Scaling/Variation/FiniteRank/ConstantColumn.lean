import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.OriginalSource
import H0mework.Versions.V2.Arithmetic.TruncatedFourier.Overlap
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

theorem radius_constant_pair (r : ℝ) (left : BurnolRadiusIntervalL2 r) :
    inner ℂ (burnolRadiusTruncatedFourier r left) (intervalConstant r) =
      inner ℂ left (burnolRadiusTruncatedFourier r (intervalConstant r)) := by
  have reflected : reflectL2 (burnolRadiusZeroExtension r (intervalConstant r)) =
      burnolRadiusZeroExtension r (intervalConstant r) := by
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
  have unitary := fourierL2.inner_map_map (burnolRadiusZeroExtension r left)
    (fourierL2 (burnolRadiusZeroExtension r (intervalConstant r)))
  rw [fourierL2_fourierL2,reflected] at unitary
  calc
    _ = inner ℂ (fourierL2 (burnolRadiusZeroExtension r left)) (burnolRadiusZeroExtension r (intervalConstant r)) :=
      (ContinuousLinearMap.adjoint_inner_right (burnolRadiusRestriction r) _ _).symm
    _ = inner ℂ (burnolRadiusZeroExtension r left) (fourierL2 (burnolRadiusZeroExtension r (intervalConstant r))) := unitary
    _ = _ := ContinuousLinearMap.adjoint_inner_left (burnolRadiusRestriction r) _ _

theorem radius_constant_chart (r : ℝ) (positive : 0<r) :
    burnolRadiusRechartEquiv positive (intervalConstant r) = (Real.sqrt r : ℂ) • e := by
  apply Lp.ext
  filter_upwards [burnolRadiusRechart_coe positive (intervalConstant r),
    (burnolRadiusScaleEquiv_measurePreserving positive).quasiMeasurePreserving.ae_eq
      (Measure.ae_smul_measure (intervalConstant_coeFn r) (ENNReal.ofReal r⁻¹)),
    Lp.coeFn_smul (Real.sqrt r : ℂ) e,intervalConstant_coeFn 1] with x chart constant scalar unit
  change (burnolRadiusRechart _ (intervalConstant r) : ℝ→ℂ) x = _
  change (intervalConstant r : ℝ→ℂ) (r*x)=1 at constant
  change (e : ℝ→ℂ) x=1 at unit
  rw [chart,constant,scalar]
  simp only [Pi.smul_apply,smul_eq_mul,unit,mul_one]

theorem recharted_constant_pair (r : ℝ) (positive : 0<r) (x : H) :
    inner ℂ e (burnolRechartedTruncatedFourierOperator r x) =
      inner ℂ (burnolRechartedTruncatedFourierOperator r e) x := by
  let A := burnolRadiusRechartEquiv positive
  let source := A.symm x
  have pair := radius_constant_pair r source
  have actual := A.inner_map_map (burnolRadiusTruncatedFourier r source) (intervalConstant r)
  have other := A.inner_map_map source (burnolRadiusTruncatedFourier r (intervalConstant r))
  have chartT (value : BurnolRadiusIntervalL2 r) :
      burnolRechartedTruncatedFourierOperator r (A value) = A (burnolRadiusTruncatedFourier r value) := by
    rw [burnolRechartedTruncatedFourierOperator_of_pos positive]
    unfold burnolRadiusRechartedTruncatedFourier
    simp only [ContinuousLinearMap.comp_apply]
    change A (burnolRadiusTruncatedFourier r (A.symm (A value))) = _
    rw [A.symm_apply_apply]
  rw [← chartT,show A source=x by exact A.apply_symm_apply x,radius_constant_chart,inner_smul_right] at actual
  rw [← chartT,show A source=x by exact A.apply_symm_apply x,radius_constant_chart,map_smul,inner_smul_right] at other
  rw [pair] at actual
  have original := actual.trans other.symm
  have sqrtNe : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne'
  have read : inner ℂ (burnolRechartedTruncatedFourierOperator r x) e = inner ℂ x (burnolRechartedTruncatedFourierOperator r e) :=
    mul_left_cancel₀ sqrtNe original
  have conjugate := congrArg (starRingEnd ℂ) read
  simpa only [inner_conj_symm] using conjugate

def p (r : ℝ) : H := Q (burnolRechartedTruncatedFourierOperator r e)
theorem actual_centered_square (r : ℝ) (positive : 0<r) :
    centeredSquare r = Q.comp (((burnolRechartedTruncatedFourierOperator r).comp
      (burnolRechartedTruncatedFourierOperator r)).comp Q) -
      (1/2 : ℂ) • InnerProductSpace.rankOne ℂ (p r) (p r) :=
  centered_square _ (recharted_constant_pair r positive)

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
