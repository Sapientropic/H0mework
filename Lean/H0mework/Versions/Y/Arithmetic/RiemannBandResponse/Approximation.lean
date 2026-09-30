import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.Band


/-! A fixed sequence of actual counted Fourier bands belongs to the original Pa
face and converges to the original Dirac-comb remainder as tempered distributions.
No Hilbert convergence or extension of the Pa projection is asserted. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaCombSourceWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem burnolPaCombSourceWidth_bounds (n : ℕ) : 0 < burnolPaCombSourceWidth n ∧ burnolPaCombSourceWidth n ≤ 1 / 2 := by
  have positive : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  constructor
  · exact one_div_pos.mpr positive
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    linarith [Nat.cast_nonneg (α := ℝ) n]

def burnolPaCombApproximation (n : ℕ) : BurnolPaAmbientCarrier :=
  ((n : ℂ) + 2) • evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (burnolReciprocalStepPhysicalState 1 (1 + burnolPaCombSourceWidth n) (by norm_num)
      (by linarith [(burnolPaCombSourceWidth_bounds n).1]) (by linarith [(burnolPaCombSourceWidth_bounds n).2]))

theorem burnolPaCombApproximation_mem (n : ℕ) :
    burnolPaCombApproximation n ∈ burnolCompactCoPoissonClosedRange := by
  apply burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
  apply burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
  apply burnolReciprocalStepWave_memPa
  linarith [(burnolPaCombSourceWidth_bounds n).2]

theorem burnolPaCombApproximation_raw (n : ℕ) :
    (burnolPaCombApproximation n : BurnolL2) =
      ((n : ℂ) + 2) • fourierL2 (burnolReciprocalStepNativeWave 1 (1 + burnolPaCombSourceWidth n)) := by
  rw [burnolReciprocalStepNativeWave_eq 1 (1 + burnolPaCombSourceWidth n) (by norm_num)
    (by linarith [(burnolPaCombSourceWidth_bounds n).1])]
  rfl

theorem burnolPaCombApproximation_Q_zero (n : ℕ) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (burnolPaCombApproximation n) = 0 :=
  Submodule.starProjection_orthogonal_apply_eq_zero (burnolPaCombApproximation_mem n)

theorem burnolPaCombApproximation_read (n : ℕ) (test : SchwartzMap ℝ ℂ) :
    (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolPaCombApproximation n : BurnolL2)) test =
      (burnolPaCombSourceWidth n)⁻¹ •
        ((Lp.toTemperedDistributionCLM ℂ volume 2
          (fourierL2 (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 (1 + burnolPaCombSourceWidth n)))) test -
          (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 burnolUnitCountingPrimitiveL2)) test) := by
  rw [burnolPaCombApproximation_raw, map_smul, smul_apply]
  have atOne : burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 1 = burnolUnitCountingPrimitiveL2 := by
    simp only [burnolSourceScalePrimitive, Real.sqrt_one, Real.log_one,
      burnolMultiplicativeDilation_zero, one_smul]
  simp only [burnolReciprocalStepNativeWave, atOne, map_sub, sub_apply]
  rw [Complex.real_smul]
  simp [burnolPaCombSourceWidth]

theorem burnolPaCombSourceWidth_tendsto_zero :
    Tendsto burnolPaCombSourceWidth atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have shifted : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
      have limit : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp shifted
      convert limit using 1
      funext n
      exact one_div ((n : ℝ) + 2)
    · exact Filter.Eventually.of_forall (fun n => (burnolPaCombSourceWidth_bounds n).1)

theorem burnolPaCombApproximation_tempered_limit :
    Tendsto (fun n => Lp.toTemperedDistributionCLM ℂ volume 2 (burnolPaCombApproximation n : BurnolL2))
      atTop (𝓝 clozelTemperedRemainder) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro test
  have derivative := (burnolCountingFourierScale_hasDerivAt test).tendsto_slope_zero_right.comp
    burnolPaCombSourceWidth_tendsto_zero
  rw [GlobalCoPoissonRoleRepresentation.coPoissonMuntzScaleRemainder_one] at derivative
  convert! derivative using 1
  funext n
  simpa only [Function.comp_apply, burnolSourceScalePrimitive, Real.sqrt_one,
    Real.log_one, burnolMultiplicativeDilation_zero, one_smul] using burnolPaCombApproximation_read n test

theorem burnolOriginalR_mem_temperedPaClosure :
    clozelTemperedRemainder ∈ closure
      ((fun state : BurnolPaAmbientCarrier =>
        Lp.toTemperedDistributionCLM ℂ volume 2 (state : BurnolL2)) ''
          (burnolCompactCoPoissonClosedRange : Set BurnolPaAmbientCarrier)) := by
  apply mem_closure_of_tendsto burnolPaCombApproximation_tempered_limit
  exact Filter.Eventually.of_forall (fun n => ⟨burnolPaCombApproximation n, burnolPaCombApproximation_mem n, rfl⟩)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
