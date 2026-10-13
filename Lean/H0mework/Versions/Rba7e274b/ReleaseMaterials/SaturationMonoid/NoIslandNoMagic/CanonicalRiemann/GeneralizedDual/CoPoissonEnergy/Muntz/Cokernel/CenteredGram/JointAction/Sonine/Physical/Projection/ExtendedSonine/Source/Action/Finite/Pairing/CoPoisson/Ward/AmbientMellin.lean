import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientFourier
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.ActionBand

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.AmbientMellin

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem gap_read (value : BurnolL2) (coefficient : ℂ)
    (gap : burnolQuarterRestriction value = coefficient • intervalConstant q) :
    (value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)] fun _ => coefficient := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
    Lp.coeFn_smul coefficient (intervalConstant q), intervalConstant_coeFn q]
      with x restricted scaled constant
  change burnolQuarterRestriction value x = value x at restricted
  rw [gap, scaled] at restricted
  simpa only [Pi.smul_apply, smul_eq_mul, constant, mul_one] using restricted.symm

/-- The original ambient reader includes the full constant gap and positive tail. -/
theorem evaluator_eq_mellin (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (coefficient : ℂ)
    (gap : burnolQuarterRestriction value = coefficient • intervalConstant q) :
    burnolAmbientCompletedMellinEvaluator coordinate value =
      mellin (value : ℝ → ℂ) (1 - coordinate.value) := by
  have localRead : (value : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 q)] fun _ => coefficient :=
    ae_restrict_of_ae_restrict_of_subset (by intro x inside; change -q ≤ x ∧ x ≤ q; constructor <;> linarith [inside.1, inside.2])
      (gap_read value coefficient gap)
  have power : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-coordinate.value)) (Ioc 0 q) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ q)).mp
      (intervalIntegral.intervalIntegrable_cpow' (by simp only [neg_re]; linarith [coordinate.belowOne]))
  have gapIntegrable : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-coordinate.value) * value x) (Ioc 0 q) := by
    apply (power.mul_const coefficient).congr
    filter_upwards [localRead] with x read
    rw [read]
  have gapIntegral : (∫ x : ℝ in Ioc 0 q, (x : ℂ) ^ (-coordinate.value) * value x) =
      burnolRadiusMellinGapMoment q coordinate.value * coefficient := by
    calc
      _ = ∫ x : ℝ in Ioc 0 q, (x : ℂ) ^ (-coordinate.value) * coefficient := by
        apply integral_congr_ae
        filter_upwards [localRead] with x read
        rw [read]
      _ = _ := by
        rw [integral_mul_const]
        have actual := integral_cpow_neg_on_burnolGap coordinate.value coordinate.belowOne
        change (∫ x : ℝ in Ioc 0 q, (x : ℂ) ^ (-coordinate.value)) =
          burnolRadiusMellinGapMoment q coordinate.value at actual
        rw [actual]
  have gapCoefficient : burnolAmbientGapCoefficient q value = coefficient := by
    change (‖intervalConstant q‖ ^ 2 : ℂ)⁻¹ * inner ℂ (intervalConstant q)
      (burnolQuarterRestriction value) = coefficient
    rw [gap, inner_smul_right, inner_self_eq_norm_sq_to_K]
    have normNe : (‖intervalConstant q‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (intervalConstant_ne_zero (by norm_num : (0 : ℝ) < q)))
    field_simp [normNe]
    ring_nf
    rfl
  have tailIntegrable := burnolRadiusMellinWeight_integrableOn_tail q (by norm_num)
    coordinate.value coordinate.rightHalf value
  change burnolRadiusMellinGapMoment q coordinate.value * burnolAmbientGapCoefficient q value +
      burnolRadiusMellinTailEvaluator q (by norm_num) coordinate.value coordinate.rightHalf value = _
  rw [gapCoefficient, burnolRadiusMellinTailEvaluator_eq_integral]
  unfold mellin
  simp only [show (1 - coordinate.value) - 1 = -coordinate.value by ring, smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ q),
    setIntegral_union (by rw [Set.disjoint_left]; intro x first second; exact (not_lt_of_ge first.2) second)
      measurableSet_Ioi gapIntegrable tailIntegrable, gapIntegral]

private theorem gap_dilation (value : BurnolL2) (coefficient : ℂ)
    (gap : burnolQuarterRestriction value = coefficient • intervalConstant q)
    (shift : ℝ) (expanding : shift ≤ 0) :
    burnolQuarterRestriction (burnolMultiplicativeDilation shift value) =
      ((Real.exp (shift / 2) : ℂ) * coefficient) • intervalConstant q := by
  have sourceRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (gap_read value coefficient gap)
  have scaled : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolMultiplicativeDilation shift value),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift value),
    ae_restrict_of_ae (scaled.ae sourceRead), ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul ((Real.exp (shift / 2) : ℂ) * coefficient) (intervalConstant q), intervalConstant_coeFn q]
      with x restricted dilated source inside smulAt constant
  have stays : Real.exp shift * x ∈ symmetricInterval q := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos (Real.exp_pos shift)]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr expanding) (abs_nonneg x)).trans
      (by simpa only [one_mul] using abs_le.mpr inside)
  change burnolQuarterRestriction (burnolMultiplicativeDilation shift value) x = _ at restricted
  rw [restricted, dilated, smulAt]
  change (Real.exp (shift / 2) : ℂ) * value (Real.exp shift * x) =
    ((Real.exp (shift / 2) : ℂ) * coefficient) * intervalConstant q x
  rw [source stays, constant, mul_one]

/-- Actual positive-axis substitution pays the moved read, including the full q contact. -/
theorem evaluator_dilation (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (coefficient : ℂ)
    (gap : burnolQuarterRestriction value = coefficient • intervalConstant q)
    (shift : ℝ) (expanding : shift ≤ 0) :
    burnolAmbientCompletedMellinEvaluator coordinate (burnolMultiplicativeDilation shift value) =
      ((Real.exp (shift / 2) : ℂ) * (Real.exp shift : ℂ) ^ (-(1 - coordinate.value))) *
        burnolAmbientCompletedMellinEvaluator coordinate value := by
  rw [evaluator_eq_mellin coordinate _ _ (gap_dilation value coefficient gap shift expanding),
    evaluator_eq_mellin coordinate value coefficient gap]
  calc
    _ = (Real.exp (shift / 2) : ℂ) *
        mellin (fun x : ℝ => value (Real.exp shift * x)) (1 - coordinate.value) := by
      unfold mellin
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift value)] with x read
      rw [read]
      change (x : ℂ) ^ _ * ((Real.exp (shift / 2) : ℂ) * value (Real.exp shift * x)) = _
      ring
    _ = _ := by rw [mellin_comp_mul_left _ _ (Real.exp_pos shift)]; simp only [smul_eq_mul]; ring

private theorem originalPa_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (value : BurnolL2)
    (member : value ∈ burnolOriginalPaInL2) :
    burnolAmbientCompletedMellinEvaluator coordinate value = 0 ∧
      ∃ coefficient : ℂ, burnolQuarterRestriction value = coefficient • intervalConstant q := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp member
  change (physical : BurnolL2) = value at actual
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have paired := (burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp orthogonal physical inPa
  have read : inner ℂ (burnolCompletedMellinRieszVector coordinate) physical = 0 := inner_eq_zero_symm.mp paired
  rw [burnolCompletedMellinRieszVector_readback] at read
  have ambient := congrArg (fun functional => functional physical)
    (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
  change burnolAmbientCompletedMellinEvaluator coordinate (physical : BurnolL2) =
    burnolCompletedMellinEvaluator coordinate physical at ambient
  have gap := burnolGenericPhysicalValue_gap physical
  refine ⟨?_, ⟨burnolConstantGapCoefficient burnolUnscaledCommonGapRadius physical, ?_⟩⟩
  · rw [← actual, ambient, read]
  · rw [← actual]
    exact gap.symm

private theorem fourier_originalPa (value : BurnolL2) (member : value ∈ burnolOriginalPaInL2) :
    fourierL2 value ∈ burnolOriginalPaInL2 := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp member
  refine Submodule.mem_map.mpr ⟨evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical,
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inPa, ?_⟩
  change fourierL2 (physical : BurnolL2) = fourierL2 value
  exact congrArg fourierL2 actual

/-- A true short source interval is expanded by its actual Mellin substitution. -/
theorem short_step_read_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (lower upper : ℝ)
    (lowerLarge : 1 ≤ lower) (ordered : lower ≤ upper) (short : upper ≤ 2 * lower) :
    burnolAmbientCompletedMellinEvaluator coordinate
      (fourierL2 (burnolReciprocalStepNativeWave lower upper)) = 0 := by
  have lowerPositive : 0 < lower := zero_lt_one.trans_le lowerLarge
  have ratioLower : 1 ≤ upper / lower := (le_div_iff₀ lowerPositive).mpr (by simpa using ordered)
  have ratioUpper : upper / lower ≤ 2 := (div_le_iff₀ lowerPositive).mpr short
  let base := fourierL2 (burnolReciprocalStepNativeWave 1 (upper / lower))
  have basePa : base ∈ burnolOriginalPaInL2 := fourier_originalPa _
    (burnolReciprocalStepNativeWave_closedPa 1 (upper / lower) (by norm_num)
      ⟨by linarith, by linarith⟩)
  obtain ⟨baseZero, coefficient, baseGap⟩ := originalPa_read coordinate zero base basePa
  have moved := evaluator_dilation coordinate base coefficient baseGap (-Real.log lower)
    (neg_nonpos.mpr (Real.log_nonneg lowerLarge))
  rw [baseZero, mul_zero] at moved
  have source := congrArg fourierL2 (burnolReciprocalStepNativeWave_dilation
    1 (upper / lower) (Real.log lower) (by norm_num) (zero_lt_one.trans_le ratioLower))
  rw [fourierL2_burnolMultiplicativeDilation, map_smul, Real.exp_log lowerPositive, one_mul,
    div_mul_cancel₀ upper lowerPositive.ne'] at source
  change burnolMultiplicativeDilation (-Real.log lower) base = _ at source
  rw [source, map_smul] at moved
  exact (smul_eq_zero.mp moved).resolve_left
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-- Exact native cocycles cover every finite source interval starting at four. -/
theorem step_read_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (upper : ℝ) (large : 4 ≤ upper) :
    burnolAmbientCompletedMellinEvaluator coordinate
      (fourierL2 (burnolReciprocalStepNativeWave 4 upper)) = 0 := by
  have bounded (n : ℕ) : ∀ upper : ℝ, 4 ≤ upper → upper ≤ 4 + n →
      burnolAmbientCompletedMellinEvaluator coordinate
        (fourierL2 (burnolReciprocalStepNativeWave 4 upper)) = 0 := by
    induction n with
    | zero =>
      intro upper lowerBound upperBound
      have same : upper = 4 := by norm_num at upperBound; exact le_antisymm upperBound lowerBound
      simp [same, burnolReciprocalStepNativeWave]
    | succ n previous =>
      intro upper lowerBound upperBound
      let middle : ℝ := 4 + n
      have middleLarge : 4 ≤ middle := by dsimp only [middle]; linarith [Nat.cast_nonneg (α := ℝ) n]
      by_cases before : upper ≤ middle
      · exact previous upper lowerBound before
      have upperShort : upper ≤ 2 * middle := by
        push_cast at upperBound
        dsimp only [middle] at *
        linarith
      have segment := short_step_read_zero coordinate zero middle upper (by linarith)
        (le_of_not_ge before) upperShort
      have head := previous middle middleLarge le_rfl
      have cocycle : burnolReciprocalStepNativeWave 4 upper =
          burnolReciprocalStepNativeWave 4 middle + burnolReciprocalStepNativeWave middle upper := by
        unfold burnolReciprocalStepNativeWave
        abel
      rw [cocycle, map_add, map_add, head, segment, add_zero]
  obtain ⟨n, beyond⟩ := exists_nat_gt upper
  exact bounded n upper large (by linarith)

/-- The complete original Bochner programme is consumed by this same ambient Mellin reader. -/
theorem original_evaluator_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolAmbientCompletedMellinEvaluator coordinate (fourierL2 (AmbientCounting.value coordinate)) = 0 := by
  let read : BurnolL2 →L[ℂ] ℂ :=
    (burnolAmbientCompletedMellinEvaluator coordinate).comp fourierL2.toLinearIsometry.toContinuousLinearMap
  have family : IntegrableOn (fun upper : ℝ => deriv (ReciprocalTail.weight coordinate) upper •
      burnolReciprocalStepNativeWave 4 upper) (Ioi 4) :=
    InfiniteWeightedProgram.family_integrable _ (ReciprocalTail.weight_deriv_measurable coordinate)
      (ReciprocalTail.derivative_weight_integrable coordinate) burnolUnitCountingPrimitiveL2
  change read (-(∫ upper : ℝ in Ioi 4, deriv (ReciprocalTail.weight coordinate) upper •
    burnolReciprocalStepNativeWave 4 upper)) = 0
  rw [map_neg, ← read.integral_comp_comm family]
  have vanishes : (∫ upper : ℝ in Ioi 4, read (deriv (ReciprocalTail.weight coordinate) upper •
      burnolReciprocalStepNativeWave 4 upper)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with upper large
    rw [map_smul]
    change _ • burnolAmbientCompletedMellinEvaluator coordinate
      (fourierL2 (burnolReciprocalStepNativeWave 4 upper)) = 0
    rw [step_read_zero coordinate zero upper large.le, smul_zero]
  rw [vanishes, neg_zero]

private theorem step_fourier_even (upper : ℝ) (large : 4 ≤ upper) :
    reflectL2 (fourierL2 (burnolReciprocalStepNativeWave 4 upper)) =
      fourierL2 (burnolReciprocalStepNativeWave 4 upper) :=
  burnolReflectL2_eq_of_even_raw _ _ (AmbientFourier.step_fourier_coeFn upper large)
    (fun x => by simp only [burnolHarmonicStepWaveRaw, burnolHarmonicStepChannels, abs_neg])

private theorem original_fourier_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (fourierL2 (AmbientCounting.value coordinate)) = fourierL2 (AmbientCounting.value coordinate) := by
  let forward : BurnolL2 →L[ℂ] BurnolL2 := fourierL2.toLinearIsometry.toContinuousLinearMap
  let reflected : BurnolL2 →L[ℂ] BurnolL2 := reflectL2.toContinuousLinearMap.comp forward
  have family : IntegrableOn (fun upper : ℝ => deriv (ReciprocalTail.weight coordinate) upper •
      burnolReciprocalStepNativeWave 4 upper) (Ioi 4) :=
    InfiniteWeightedProgram.family_integrable _ (ReciprocalTail.weight_deriv_measurable coordinate)
      (ReciprocalTail.derivative_weight_integrable coordinate) burnolUnitCountingPrimitiveL2
  change reflected (-(∫ upper : ℝ in Ioi 4, deriv (ReciprocalTail.weight coordinate) upper •
      burnolReciprocalStepNativeWave 4 upper)) =
    forward (-(∫ upper : ℝ in Ioi 4, deriv (ReciprocalTail.weight coordinate) upper •
      burnolReciprocalStepNativeWave 4 upper))
  rw [map_neg, map_neg, ← reflected.integral_comp_comm family, ← forward.integral_comp_comm family]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with upper large
  simp only [map_smul]
  change _ • reflectL2 (fourierL2 (burnolReciprocalStepNativeWave 4 upper)) =
    _ • fourierL2 (burnolReciprocalStepNativeWave 4 upper)
  rw [step_fourier_even upper large.le]

/-- The original zeta zero annihilates this actual full Fourier-source/Mellin-kernel pairing. -/
theorem original_fourier_pair_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (fourierL2 (AmbientCounting.value coordinate))
      (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)) = 0 := by
  let value := fourierL2 (AmbientCounting.value coordinate)
  let kernel := burnolAmbientCompletedMellinKernelFormula coordinate
  have kernelRead : inner ℂ kernel value = 0 := by
    dsimp only [kernel]
    rw [← burnolAmbientCompletedMellinRieszVector_eq_kernelFormula,
      burnolAmbientCompletedMellinRieszVector_readback]
    exact original_evaluator_zero coordinate zero
  have reflectedRead : inner ℂ (reflectL2 kernel) value = 0 := by
    calc
      _ = inner ℂ (reflectL2 kernel) (reflectL2 value) := by dsimp only [value]; rw [original_fourier_even coordinate]
      _ = _ := (reflectL2.inner_map_map kernel value).trans kernelRead
  apply inner_eq_zero_symm.mp
  change inner ℂ ((1 / 2 : ℂ) • (kernel + reflectL2 kernel)) value = 0
  rw [inner_smul_left, inner_add_left, kernelRead, reflectedRead, add_zero, mul_zero]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.AmbientMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
