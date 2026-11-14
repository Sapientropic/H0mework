import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactPhaseWave

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open FourierTransform
open scoped FourierTransform BoundedContinuousFunction InnerProductSpace

open private centre_integrable homogeneous_tail_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit
open private centre_seed_integrable seed_exterior_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseInput
open private mean_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open private quarter_cut_identity compact_join_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactPhaseWave


local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "H" => countedHomogeneousSplit
local notation "A" => fun c => burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "power" => fun c (x : ℝ) => ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ)

private theorem homogeneous_position_read (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, (H c).1 x+(H c).2 x = power c x := by
  filter_upwards [(centre_integrable c).coeFn_toL1, homogeneous_tail_read c] with x inner outer
  change (H c).1 x = Set.indicator (symmetricInterval r₀) (power c) x at inner
  change (H c).2 x = (if r₀ < |x| then power c x else 0) at outer
  rw [inner, outer]
  by_cases small : x ∈ symmetricInterval r₀
  · rw [indicator_of_mem small, if_neg (not_lt_of_ge (abs_le.mpr small)), add_zero]
  · rw [indicator_of_notMem small, if_pos (lt_of_not_ge fun h => small (abs_le.mp h)), zero_add]

private theorem seed_position_read (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, (countedSeedSplit c).1 x+(countedSeedSplit c).2 x =
      Set.indicator (symmetricInterval q) (seedRaw c.value) x := by
  filter_upwards [(centre_seed_integrable c).coeFn_toL1, seed_exterior_read c] with x inner outer
  change (countedSeedSplit c).1 x = _ at inner
  change (countedSeedSplit c).2 x = _ at outer
  rw [inner, outer]
  by_cases large : x ∈ symmetricInterval q
  · rw [indicator_of_mem large]
    by_cases small : x ∈ symmetricInterval r₀
    · rw [indicator_of_mem small, if_neg (fun h => (not_lt_of_ge (abs_le.mpr small)) h.1), add_zero]
    · rw [indicator_of_notMem small, if_pos ⟨lt_of_not_ge fun h => small (abs_le.mp h), abs_le.mpr large⟩, zero_add]
  · have outside : q < |x| := lt_of_not_ge fun h => large (abs_le.mp h)
    have small : x ∉ symmetricInterval r₀ := fun h =>
      outside.not_ge ((abs_le.mpr h).trans (by norm_num))
    rw [indicator_of_notMem small, indicator_of_notMem large, if_neg (fun h => outside.not_ge h.2), add_zero]

private theorem seed_quarter_supported (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, q < |x| → (countedSeedSplit c).2 x = 0 := by
  filter_upwards [seed_exterior_read c] with x read outside
  change (countedSeedSplit c).2 x = _ at read
  rw [read, if_neg (fun h => outside.not_ge h.2)]

private theorem ambient_homogeneous_read (c : BurnolCompletedMellinCoordinate) :
    (A c : ℝ → ℂ) =ᵐ[volume]
      fun x => if |x| ≤ q then GapEuler.gapMean q c else power c x := by
  have raw := burnolEvenRaw_ae _ _ (burnolAmbientMellinKernel_ae_raw c)
  filter_upwards [raw] with x read
  rw [read]
  unfold burnolEvenRaw burnolAmbientMellinKernelRaw burnolGapRieszRaw burnolRadiusMellinTailKernelRaw
  rw [burnolIntervalConstant_norm_sq (by norm_num : 0 < q)]
  by_cases inside : |x| ≤ q
  · have member : x ∈ symmetricInterval q := abs_le.mp inside
    have reflected : -x ∈ symmetricInterval q := abs_le.mp (by simpa only [abs_neg] using inside)
    have right : x ∉ Ioi q := not_lt_of_ge ((le_abs_self x).trans inside)
    have left : -x ∉ Ioi q := not_lt_of_ge ((neg_le_abs x).trans inside)
    rw [indicator_of_mem member, indicator_of_mem reflected, if_neg right, if_neg left]
    simp only [mul_one, add_zero, if_pos inside, GapEuler.gapMean, star_inv₀,
      Complex.star_def, Complex.conj_ofReal]
    ring
  · have outside : q < |x| := lt_of_not_ge inside
    have missing : x ∉ symmetricInterval q := fun h => inside (abs_le.mpr h)
    have reflected : -x ∉ symmetricInterval q := fun h => inside (by simpa only [abs_neg] using abs_le.mpr h)
    rw [indicator_of_notMem missing, indicator_of_notMem reflected, mul_zero, mul_zero, zero_add, zero_add, if_neg inside]
    rcases lt_or_gt_of_ne (abs_pos.mp ((by norm_num : 0 < q).trans outside)) with negative | positive
    · rw [abs_of_neg negative] at outside
      have left : -x ∈ Ioi q := outside
      have right : x ∉ Ioi q := not_lt_of_ge (negative.le.trans (by norm_num))
      rw [if_neg right, if_pos left, zero_add]
      change (1/2 : ℂ) * ((-x : ℝ) : ℂ)^(-s₀ c) = ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ)
      rw [abs_of_neg negative, mul_comm]
    · rw [abs_of_pos positive] at outside
      have right : x ∈ Ioi q := outside
      have left : -x ∉ Ioi q := not_lt_of_ge ((neg_nonpos.mpr positive.le).trans (by norm_num))
      rw [if_pos right, if_neg left, add_zero]
      change (1/2 : ℂ) * (x : ℂ)^(-s₀ c) = ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ)
      rw [abs_of_pos positive, mul_comm]

private theorem seed_join_read (c : BurnolCompletedMellinCoordinate) :
    (compactPhaseJoin (countedSeedSplit c) : ℝ → ℂ) =ᵐ[volume]
      Set.indicator (symmetricInterval q) (seedRaw c.value) :=
  (compact_join_read _ (quarter_cut_identity _ (seed_quarter_supported c))).trans (seed_position_read c)

/-- The complete homogeneous position field is the original ambient kernel
plus the actual compact seed of the phase source. -/
theorem actual_counted_homogeneous_position_split (c : BurnolCompletedMellinCoordinate) :
    distributionOfSplit (H c) = (A c : S')+distributionOfSplit (countedSeedSplit c) := by
  let seed := compactPhaseJoin (countedSeedSplit c)
  have joined := compact_join_read _ (quarter_cut_identity _ (seed_quarter_supported c))
  have seedDist : distributionOfSplit (countedSeedSplit c) = (seed : S') := by
    ext test
    rw [distributionOfSplit_apply, Lp.toTemperedDistribution_apply]
    simp only [smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [joined] with x read
    rw [read]
  ext test
  rw [seedDist, add_apply, distributionOfSplit_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  have ambient : Integrable (fun x => test x*A c x) :=
    (test.memLp 2).integrable_mul (Lp.memLp (A c))
  have core : Integrable (fun x => test x*seed x) :=
    (L1.integrable_coeFn seed).mul_of_top_right test.memLp_top
  rw [← integral_add ambient core]
  apply integral_congr_ae
  filter_upwards [homogeneous_position_read c, ambient_homogeneous_read c, seed_join_read c]
    with x hom atAmbient atSeed
  change test x*((H c).1 x+(H c).2 x) = test x*A c x+test x*compactPhaseJoin (countedSeedSplit c) x
  rw [hom, ← mul_add, atAmbient, atSeed]
  by_cases inside : x ∈ symmetricInterval q
  · rw [if_pos (abs_le.mpr inside), indicator_of_mem inside]
    unfold seedRaw powerRaw
    have mean := mean_power c
    change test x*(((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ)) =
      test x*(GapEuler.gapMean q c+(1/2 : ℂ)*(((|x| : ℝ) : ℂ)^(-s₀ c)-rawMean (fun x => ((|x| : ℝ) : ℂ)^(-s₀ c))))
    change (1/2 : ℂ)*rawMean (fun x => ((|x| : ℝ) : ℂ)^(-s₀ c)) = _ at mean
    linear_combination (test x)*mean
  · rw [if_neg (fun h => inside (abs_le.mp h)), indicator_of_notMem inside, add_zero]

theorem actual_counted_seed_wave_read (c : BurnolCompletedMellinCoordinate) (ξ : ℝ) :
    compactPhaseWave (countedSeedSplit c) ξ = Constructor.fourierRaw (seedRaw c.value) ξ := by
  change (𝓕 (compactPhaseJoin (countedSeedSplit c) : ℝ → ℂ)) ξ = _
  rw [Real.fourier_congr_ae (seed_join_read c) ξ, Real.fourier_eq]
  unfold Constructor.fourierRaw VectorFourier.fourierIntegral
  rw [← integral_indicator (measurableSet_symmetricInterval q)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside]; rfl
  · rw [indicator_of_notMem inside, indicator_of_notMem inside, smul_zero]

/-- The literal homogeneous wave keeps both original components of its forcing. -/
theorem actual_counted_homogeneous_wave_split (c : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    𝓕 (distributionOfSplit (H c)) test =
      (ForcingWhole.whole c : S') test+∫ ξ, test ξ*compactPhaseWave (countedSeedSplit c) ξ := by
  rw [actual_counted_homogeneous_position_split, FourierAdd.fourier_add, add_apply,
    compact_phase_wave_tempered _ (seed_quarter_supported c)]
  rw [Lp.fourier_toTemperedDistribution_eq]; rfl

private theorem wave_test_integrable (wave : ℝ →ᵇ ℂ) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x => test x*wave x) := by
  apply (test.integrable.norm.mul_const ‖wave‖).mono'
    (test.continuous.mul wave.continuous).aestronglyMeasurable
  filter_upwards with x
  change ‖test x*wave x‖ ≤ ‖test x‖*‖wave‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (wave.norm_coe_le_norm x) (norm_nonneg _)

theorem actual_counted_homogeneous_wave_power (c : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    𝓕 (distributionOfSplit (H c)) test =
      ∫ ξ : ℝ, test ξ*(ForcingPrimitive.leadingCoefficient c*((|ξ| : ℝ) : ℂ)^(s₀ c-1)) := by
  rw [actual_counted_homogeneous_wave_split, Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  have whole : Integrable (fun x => test x*ForcingWhole.whole c x) :=
    (test.memLp 2).integrable_mul (Lp.memLp (ForcingWhole.whole c))
  rw [← integral_add whole (wave_test_integrable _ test)]
  apply integral_congr_ae
  filter_upwards [ForcingWhole.whole_read c, volume.ae_ne (0 : ℝ)] with x forcing nonzero
  rw [← mul_add, forcing, actual_counted_seed_wave_read, actual_seed_fourier_balance_abs c x nonzero]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
