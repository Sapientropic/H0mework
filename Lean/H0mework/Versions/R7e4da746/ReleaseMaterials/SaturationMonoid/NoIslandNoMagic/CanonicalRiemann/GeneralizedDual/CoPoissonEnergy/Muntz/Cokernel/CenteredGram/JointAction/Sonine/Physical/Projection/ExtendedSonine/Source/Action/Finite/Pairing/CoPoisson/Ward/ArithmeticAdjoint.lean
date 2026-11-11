import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WholeSourceWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticAdjoint

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource InverseAction
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem extension_restriction_read (value : BurnolL2) :
    (burnolQuarterZeroExtension (burnolQuarterRestriction value) : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval q).indicator (value : ℝ → ℂ) := by
  have restricted := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value)
  filter_upwards [burnolQuarterZeroExtension_coe (burnolQuarterRestriction value), restricted]
    with x extension source
  rw [extension]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside]
    exact source inside
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private theorem dilation_restriction (value : BurnolL2) (shift : ℝ) (expanding : shift ≤ 0) :
    burnolQuarterRestriction (burnolMultiplicativeDilation shift
      (burnolQuarterZeroExtension (burnolQuarterRestriction value))) =
    burnolQuarterRestriction (burnolMultiplicativeDilation shift value) := by
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolMultiplicativeDilation shift (burnolQuarterZeroExtension (burnolQuarterRestriction value))),
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolMultiplicativeDilation shift value),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift
      (burnolQuarterZeroExtension (burnolQuarterRestriction value))),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift value),
    ae_restrict_of_ae (scale.ae (extension_restriction_read value)),
    ae_restrict_mem (measurableSet_symmetricInterval q)]
      with x left right leftAction rightAction source inside
  have stays : Real.exp shift * x ∈ symmetricInterval q := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos (Real.exp_pos shift)]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr expanding) (abs_nonneg x)).trans
      (by simpa only [one_mul] using abs_le.mpr inside)
  change burnolQuarterRestriction _ x = _ at left right
  rw [left, right, leftAction, rightAction]
  change (Real.exp (shift / 2) : ℂ) * _ = (Real.exp (shift / 2) : ℂ) * _
  rw [source, indicator_of_mem stays]

/-- For scales at least one, every sampled x / scale stays in the original q-window. -/
theorem counting_fourier (scale : ℝ) (large : 1 ≤ scale) (state : BurnolQuarterIntervalL2) :
    countingWindow scale (burnolTruncatedFourier state) =
      (Real.sqrt scale : ℂ)⁻¹ • burnolQuarterRestriction
        (burnolMultiplicativeDilation (-Real.log scale) (fourierL2 (burnolQuarterZeroExtension state))) := by
  unfold countingWindow
  change (Real.sqrt scale : ℂ)⁻¹ • burnolQuarterRestriction
      (burnolMultiplicativeDilation (-Real.log scale)
        (burnolQuarterZeroExtension (burnolQuarterRestriction (fourierL2 (burnolQuarterZeroExtension state))))) = _
  rw [dilation_restriction _ _ (neg_nonpos.mpr (Real.log_nonneg large))]

/-- Fourier's actual independent dual and its inverse dilation generate this symmetric reading.
Only the right test needs reflection invariance. -/
theorem counting_fourier_pairing (scale : ℝ) (large : 1 ≤ scale)
    (left right : BurnolQuarterIntervalL2) (rightEven : reflectRestricted q right = right) :
    inner ℂ (countingWindow scale (burnolTruncatedFourier left)) right =
      inner ℂ left (countingWindow scale (burnolTruncatedFourier right)) := by
  have reflected : reflectL2 (burnolQuarterZeroExtension right) = burnolQuarterZeroExtension right := by
    change reflectL2 (burnolRadiusZeroExtension q right) = _
    rw [burnolRadiusZeroExtension_reflect, rightEven]
    rfl
  have movedEven : reflectL2 (burnolMultiplicativeDilation (Real.log scale)
      (burnolQuarterZeroExtension right)) =
      burnolMultiplicativeDilation (Real.log scale) (burnolQuarterZeroExtension right) := by
    rw [reflectL2_burnolMultiplicativeDilation, reflected]
  have unitary := fourierL2.inner_map_map (burnolQuarterZeroExtension left)
    (fourierL2 (burnolMultiplicativeDilation (Real.log scale) (burnolQuarterZeroExtension right)))
  rw [fourierL2_fourierL2, movedEven, fourierL2_burnolMultiplicativeDilation] at unitary
  have flipped := (burnolMultiplicativeDilation (-Real.log scale)).inner_map_eq_flip
    (fourierL2 (burnolQuarterZeroExtension left)) (burnolQuarterZeroExtension right)
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at flipped
  rw [counting_fourier scale large left, counting_fourier scale large right,
    inner_smul_left, inner_smul_right]
  simp only [map_inv₀, Complex.conj_ofReal]
  congr 1
  calc
    _ = inner ℂ (burnolMultiplicativeDilation (-Real.log scale) (fourierL2 (burnolQuarterZeroExtension left)))
        (burnolQuarterZeroExtension right) :=
      (ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ right).symm
    _ = inner ℂ (fourierL2 (burnolQuarterZeroExtension left))
        (burnolMultiplicativeDilation (Real.log scale) (burnolQuarterZeroExtension right)) := flipped
    _ = inner ℂ (burnolQuarterZeroExtension left)
        (burnolMultiplicativeDilation (-Real.log scale) (fourierL2 (burnolQuarterZeroExtension right))) := unitary
    _ = _ := ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ left

/-- The original b and its actual return are consumed without commuting S past counting. -/
theorem original_cross_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    inner ℂ (countingWindow scale (WholeSourceWindow.smoothState coordinate))
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
    inner ℂ (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
      (countingWindow scale (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) :=
  counting_fourier_pairing scale large _ _ (burnolRieszSingleFourierSource_reflection_fixed coordinate)

/-- For the original return, the complete mean term is constant after each integer-scale action
and is paid by the return's original mean-zero property. -/
theorem original_return_counting_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    inner ℂ (countingWindow scale (WholeSourceWindow.smoothState coordinate))
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
    inner ℂ (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
      (countingWindow scale (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) := by
  let b := (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let r := Constructor.returnState coordinate
  let mean := burnolQuarterMeanCoefficient (burnolTruncatedFourier b)
  have source : burnolTruncatedFourier b = (r : BurnolQuarterIntervalL2) + mean • intervalConstant q := by
    have original := burnolMeanZeroProjection_eq_sub_constant (burnolTruncatedFourier b)
    change (r : BurnolQuarterIntervalL2) = burnolTruncatedFourier b - mean • intervalConstant q at original
    rw [original]
    abel
  have counted : countingWindow scale (burnolTruncatedFourier b) =
      countingWindow scale (r : BurnolQuarterIntervalL2) +
        (mean * (scale : ℂ)⁻¹) • intervalConstant q := by
    rw [source]
    have linear : countingWindow scale ((r : BurnolQuarterIntervalL2) + mean • intervalConstant q) =
        countingWindow scale (r : BurnolQuarterIntervalL2) + mean • countingWindow scale (intervalConstant q) := by
      simp only [countingWindow, map_add, map_smul, smul_add, smul_smul]
      module
    rw [linear, SingularCounting.counting_constant scale large, smul_smul]
  have constantZero : inner ℂ (r : BurnolQuarterIntervalL2) (intervalConstant q) = 0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp r.property _ (Submodule.mem_span_singleton_self _))
  rw [original_cross_pairing coordinate scale large]
  change inner ℂ (r : BurnolQuarterIntervalL2) (countingWindow scale (burnolTruncatedFourier b)) = _
  rw [counted, inner_add_right, inner_smul_right, constantZero, mul_zero, add_zero]

/-- The finite arithmetic tail keeps both actual sides of the independently generated dual. -/
theorem original_finite_cross_pairing (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    inner ℂ (∑ n ∈ Finset.Ico 1 N, countingWindow (n : ℝ) (WholeSourceWindow.smoothState coordinate))
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
    inner ℂ (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
      (∑ n ∈ Finset.Ico 1 N, countingWindow (n : ℝ) (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) := by
  rw [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro n inside
  exact original_cross_pairing coordinate n (by exact_mod_cast (Finset.mem_Ico.mp inside).1)

/-- The actual smooth-source series supplies the whole scalar dual tail.
No summability of the vector series on the right is assumed. -/
theorem original_cross_hasSum (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun n : ℕ => inner ℂ (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
      (countingWindow (n : ℝ) (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))))
      (inner ℂ (∑' n : ℕ, countingWindow (n : ℝ) (WholeSourceWindow.smoothState coordinate))
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  have source := (WholeSourceWindow.smooth_window_summable coordinate).hasSum.mapL
    (innerSLFlip ℂ (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))
  apply source.congr_fun
  intro n
  by_cases zero : n = 0
  · simp [zero, countingWindow]
  · exact (original_cross_pairing coordinate n (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)).symm

/-- The source-generated scalar quadratic tail converges even without assigning a vector sum to C_n r. -/
theorem original_return_hasSum (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun n : ℕ => inner ℂ (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
      (countingWindow (n : ℝ) (Constructor.returnState coordinate : BurnolQuarterIntervalL2)))
      (inner ℂ (∑' n : ℕ, countingWindow (n : ℝ) (WholeSourceWindow.smoothState coordinate))
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  have source := (WholeSourceWindow.smooth_window_summable coordinate).hasSum.mapL
    (innerSLFlip ℂ (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))
  apply source.congr_fun
  intro n
  by_cases zero : n = 0
  · simp [zero, countingWindow]
  · exact (original_return_counting_pairing coordinate n (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)).symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticAdjoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
