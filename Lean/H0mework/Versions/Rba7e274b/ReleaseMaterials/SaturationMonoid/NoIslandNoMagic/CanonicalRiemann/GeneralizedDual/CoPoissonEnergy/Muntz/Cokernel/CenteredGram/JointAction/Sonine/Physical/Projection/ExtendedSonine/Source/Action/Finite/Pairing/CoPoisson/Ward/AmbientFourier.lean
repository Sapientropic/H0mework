import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientCounting
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.HarmonicRealization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.AmbientFourier

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszSource.Translator
noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem step_weighted_integrable (upper : ℝ) (large : 4 ≤ upper) (power : ℕ) :
    Integrable (fun x : ℝ => ‖burnolReciprocalStepSourceRaw 4 upper x‖ / |x| ^ power) := by
  have envelope : Integrable ((symmetricInterval q).indicator
      (fun _ : ℝ => upper ^ (power + 1))) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      (measurableSet_symmetricInterval q)
  apply envelope.mono'
    (((burnolReciprocalStepSource_measurable 4 upper).norm.div
      (by fun_prop : Measurable (fun x : ℝ => |x| ^ power))).aestronglyMeasurable)
  filter_upwards with x
  change ‖‖burnolReciprocalStepSourceRaw 4 upper x‖ / |x| ^ power‖ ≤
    (symmetricInterval q).indicator (fun _ : ℝ => upper ^ (power + 1)) x
  by_cases active : 4 ≤ |x|⁻¹ ∧ |x|⁻¹ < upper
  · have positive : 0 < |x| := inv_pos.mp ((by norm_num : (0 : ℝ) < 4).trans_le active.1)
    have inside : x ∈ symmetricInterval q := by
      apply abs_le.mp
      simpa only [inv_eq_one_div] using
        (le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) positive).mp active.1
    rw [indicator_of_mem inside, Real.norm_of_nonneg (by positivity),
      burnolReciprocalStepSourceRaw, if_pos active, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_abs, div_eq_mul_inv, ← inv_pow]
    calc
      _ = (|x|⁻¹) ^ (power + 1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) active.2.le _
  · rw [burnolReciprocalStepSourceRaw, if_neg active, norm_zero, zero_div, norm_zero]
    exact indicator_nonneg (fun _ _ => pow_nonneg (by linarith) _) x

private theorem step_reciprocal_integrable (upper : ℝ) (large : 4 ≤ upper) :
    IntegrableOn (fun x : ℝ => (x : ℂ)⁻¹ * burnolReciprocalStepSourceRaw 4 upper x) (Ioi 0) := by
  have normRead (x : ℝ) : ‖(x : ℂ)⁻¹ * burnolReciprocalStepSourceRaw 4 upper x‖ =
      ‖burnolReciprocalStepSourceRaw 4 upper x‖ / |x| := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
  have normIntegral : Integrable (fun x : ℝ =>
      ‖(x : ℂ)⁻¹ * burnolReciprocalStepSourceRaw 4 upper x‖) := by
    simpa only [normRead, pow_one] using step_weighted_integrable upper large 1
  exact ((integrable_norm_iff
    ((Complex.measurable_ofReal.comp measurable_id).inv.mul
      (burnolReciprocalStepSource_measurable 4 upper)).aestronglyMeasurable).mp normIntegral).integrableOn

/-- The actual finite support pays the source integrals for every finite upper endpoint. -/
theorem step_realizes (upper : ℝ) (large : 4 ≤ upper) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolReciprocalStepNativeSource 4 upper) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolReciprocalStepNativeWave 4 upper)) test := by
  rw [burnolReciprocalStepNativeSource_eq 4 upper (by norm_num) large,
    burnolReciprocalStepNativeWave_eq 4 upper (by norm_num) large]
  have actual := burnolRemainderSourceRead_forward
    (burnolReciprocalStepSourceL2 4 upper (by norm_num) large)
    (burnolReciprocalStepSourceRaw 4 upper) (burnolReciprocalStepSource_measurable 4 upper)
    (burnolReciprocalStepSource_memLp 4 upper (by norm_num) large).coeFn_toLp
    (by simp [burnolReciprocalStepSourceRaw])
    (fun x => by simp only [burnolReciprocalStepSourceRaw, abs_neg])
    (step_weighted_integrable upper large 3) (step_reciprocal_integrable upper large) test
  rw [actual, burnolReciprocalStepSource_reciprocalMean 4 upper (by norm_num) large]
  simp_rw [← burnolReciprocalStepWave_coSum 4 upper _ (by norm_num)]
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(burnolReciprocalStepWave_memLp 4 upper (by norm_num) large).coeFn_toLp]
    with x read
  change burnolReciprocalStepWaveL2 4 upper (by norm_num) large x = _ at read
  rw [read]
  rfl

theorem weighted_realizes (upper : ℝ) (large : 4 ≤ upper) (f f' : ℝ → ℂ)
    (regular : ContinuousOn f' (Icc 4 upper)) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolWeightedReciprocalStepSource 4 upper f f') test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolWeightedReciprocalStepWave 4 upper f f')) test := by
  have sourceContinuous : ContinuousOn (burnolReciprocalStepNativeSource 4) (Icc 4 upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitReciprocalPrimitiveL2).mono
      (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans_le inside.1)).sub continuousOn_const
  have waveContinuous : ContinuousOn (burnolReciprocalStepNativeWave 4) (Icc 4 upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitCountingPrimitiveL2).mono
      (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans_le inside.1)).sub continuousOn_const
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc 4 upper), ∀ ψ : SchwartzMap ℝ ℂ,
      burnolRemainderSourceRead (f' u • burnolReciprocalStepNativeSource 4 u) ψ =
        (Lp.toTemperedDistributionCLM ℂ volume 2 (f' u • burnolReciprocalStepNativeWave 4 u)) ψ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    intro ψ
    rw [← burnolRemainderSourceReadCLM_apply, map_smul,
      burnolRemainderSourceReadCLM_apply, step_realizes u inside.1.le]
    simp only [map_smul, smul_apply, smul_eq_mul]
  have integralRead := burnolRemainderSourceRead_bochner (volume.restrict (Ioc 4 upper))
    (fun u => f' u • burnolReciprocalStepNativeSource 4 u)
    (fun u => f' u • burnolReciprocalStepNativeWave 4 u)
    ((regular.smul sourceContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((regular.smul waveContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self) familyRead test
  rw [burnolWeightedReciprocalStepSource, ← burnolRemainderSourceReadCLM_apply,
    map_sub, map_smul, burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    step_realizes upper large, integralRead]
  simp only [burnolWeightedReciprocalStepWave, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]

theorem step_fourier_coeFn (upper : ℝ) (large : 4 ≤ upper) :
    (fourierL2 (burnolReciprocalStepNativeWave 4 upper) : ℝ → ℂ) =ᵐ[volume]
      burnolHarmonicStepWaveRaw 4 upper := by
  let source := burnolTateReciprocalL2 (burnolReciprocalStepNativeSource 4 upper)
  let value := fourierL2 (burnolReciprocalStepNativeWave 4 upper)
  have represents : (source : ℝ → ℂ) =ᵐ[volume] burnolTateStepBoxRaw 4 upper := by
    dsimp only [source]
    rw [burnolReciprocalStepNativeSource_eq 4 upper (by norm_num) large]
    exact burnolReciprocalStepSource_tate_raw 4 upper (by norm_num) large
  have even : reflectL2 source = source := burnolReflectL2_eq_of_even_raw source _ represents
    (fun x => by simp only [burnolTateStepBoxRaw, abs_neg])
  have gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae represents,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
    rw [read, burnolTateStepBoxRaw]
    exact if_neg (fun active => by linarith [abs_le.mpr inside, active.1])
  have realization (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * value x := by
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      burnolRemainderRealization_fourier (burnolReciprocalStepNativeSource 4 upper)
        (burnolReciprocalStepNativeWave 4 upper) (step_realizes upper large) test
  obtain ⟨raw, rawRep, _, valueRep⟩ :=
    burnolRemainderSourceRead_realization_ae source value even gap realization
  have same := rawRep.symm.trans represents
  have coSum := burnolInnerGapForward_ae_congr raw (burnolTateStepBoxRaw 4 upper) same
  have mean : (∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) = (Real.log (upper / 4) : ℂ) := by
    calc
      _ = ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * burnolTateStepBoxRaw 4 upper u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae same] with u read
        rw [read]
      _ = _ := burnolTateStepBox_reciprocalMean 4 upper (by norm_num) large
  filter_upwards [valueRep, coSum] with x valueAt sumAt
  rw [valueAt, sumAt, mean, burnolTateStepBox_finiteCoSum 4 upper x (by norm_num)
    ((by norm_num : (0 : ℝ) < 4).trans_le large)]
  rfl

theorem step_fourier_restriction (upper : ℝ) (large : 4 ≤ upper) :
    burnolQuarterRestriction (fourierL2 (burnolReciprocalStepNativeWave 4 upper)) =
      -(Real.log (upper / 4) : ℂ) • intervalConstant q := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
    (fourierL2 (burnolReciprocalStepNativeWave 4 upper)),
    ae_restrict_of_ae (step_fourier_coeFn upper large),
    ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul (-(Real.log (upper / 4) : ℂ)) (intervalConstant q), intervalConstant_coeFn q]
      with x restricted read inside smulAt constantAt
  change burnolQuarterRestriction (fourierL2 (burnolReciprocalStepNativeWave 4 upper)) x = _ at restricted
  rw [restricted, read, smulAt]
  change burnolHarmonicStepWaveRaw 4 upper x = -(Real.log (upper / 4) : ℂ) * intervalConstant q x
  rw [constantAt, mul_one]
  have index : ⌊|x| / 4⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith [abs_le.mpr inside])
  have channels : burnolHarmonicStepChannels 4 upper x = ∅ := by
    unfold burnolHarmonicStepChannels
    rw [index]
    exact Finset.Ioc_eq_empty_of_le (Nat.zero_le _)
  simp only [burnolHarmonicStepWaveRaw, channels, Finset.sum_empty, zero_sub]

/-- The complete finite Fourier contact is the weighted logarithmic mean. -/
theorem weighted_fourier_restriction (upper : ℝ) (large : 4 ≤ upper) (f f' : ℝ → ℂ)
    (regular : ContinuousOn f' (Icc 4 upper)) :
    burnolQuarterRestriction (fourierL2 (burnolWeightedReciprocalStepWave 4 upper f f')) =
      -(f upper * (Real.log (upper / 4) : ℂ) -
        ∫ u : ℝ in Ioc 4 upper, f' u * (Real.log (u / 4) : ℂ)) • intervalConstant q := by
  let read : BurnolL2 →L[ℂ] BurnolQuarterIntervalL2 :=
    burnolQuarterRestriction.comp fourierL2.toLinearIsometry.toContinuousLinearMap
  have family : IntegrableOn (fun u => f' u • burnolReciprocalStepNativeWave 4 u) (Ioc 4 upper) :=
    OriginalRieszFinitePairing.CoPoisson.Energy.stepWave_integrable 4 upper f' (by norm_num) regular
  change read (burnolWeightedReciprocalStepWave 4 upper f f') = _
  rw [burnolWeightedReciprocalStepWave, map_sub, map_smul, ← read.integral_comp_comm family]
  have head : read (burnolReciprocalStepNativeWave 4 upper) =
      -(Real.log (upper / 4) : ℂ) • intervalConstant q := step_fourier_restriction upper large
  rw [head]
  have integralRead : (∫ u : ℝ in Ioc 4 upper, read (f' u • burnolReciprocalStepNativeWave 4 u)) =
      (∫ u : ℝ in Ioc 4 upper, -(f' u * (Real.log (u / 4) : ℂ))) • intervalConstant q := by
    rw [← integral_smul_const]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u inside
    dsimp only
    rw [map_smul]
    change f' u • burnolQuarterRestriction (fourierL2 (burnolReciprocalStepNativeWave 4 u)) = _
    rw [step_fourier_restriction u inside.1.le, smul_smul, mul_neg]
  rw [integralRead, integral_neg, smul_smul, mul_neg, ← sub_smul]
  congr 1
  ring

theorem original_realizes (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (AmbientCounting.value coordinate)) test := by
  have sourceLimit := ((burnolRemainderSourceReadCLM test).continuous.tendsto _).comp
    (ReciprocalSeed.seed_tendsto coordinate)
  have continuousRead : Continuous (fun value : BurnolL2 =>
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) := by fun_prop
  have waveLimit := (continuousRead.tendsto _).comp
    (InfiniteWeightedProgram.finite_program_tendsto (ReciprocalTail.weight coordinate)
      (deriv (ReciprocalTail.weight coordinate)) (ReciprocalTail.weight_deriv_measurable coordinate)
      (ReciprocalTail.derivative_weight_integrable coordinate) (ReciprocalTail.head_tendsto_zero coordinate)
      burnolUnitCountingPrimitiveL2)
  have actual := sourceLimit.congr' (show _ =ᶠ[atTop]
      (fun upper : ℝ => (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolWeightedReciprocalStepWave 4 upper (ReciprocalTail.weight coordinate)
          (deriv (ReciprocalTail.weight coordinate)))) test) from by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper large
    dsimp only [Function.comp_apply]
    rw [burnolRemainderSourceReadCLM_apply]
    exact weighted_realizes upper large _ _ ((ReciprocalTail.weight_deriv_continuousOn coordinate).mono
      (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans_le inside.1)) test)
  simp only [WeightedProgram.program_original] at waveLimit
  simpa only [burnolRemainderSourceReadCLM_apply, AmbientCounting.value]
      using tendsto_nhds_unique actual waveLimit

private def sourceRaw (coordinate : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate)

private theorem sourceRaw_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
      ℝ → ℂ) =ᵐ[volume] sourceRaw coordinate := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolRieszSingleFourierSource_ae_raw coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2), localRead] with x extendedAt rawAt
  rw [extendedAt]
  by_cases inside : x ∈ symmetricInterval q
  · simp only [sourceRaw, indicator_of_mem inside, rawAt inside]
  · simp only [sourceRaw, indicator_of_notMem inside]

private theorem sourceRaw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    sourceRaw coordinate (-x) = sourceRaw coordinate x := by
  have same : -x ∈ symmetricInterval q ↔ x ∈ symmetricInterval q := by
    change -q ≤ -x ∧ -x ≤ q ↔ -q ≤ x ∧ x ≤ q
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  unfold sourceRaw
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem (same.mpr inside), OriginalRieszFinitePairing.source_raw_even]
  · rw [indicator_of_notMem inside, indicator_of_notMem (fun negInside => inside (same.mp negInside))]

private theorem sourceRaw_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (sourceRaw coordinate) :=
  (burnolQuarterZeroExtensionRaw_integrable
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)).congr
      ((burnolQuarterZeroExtension_coe _).symm.trans (sourceRaw_read coordinate))

private theorem sourceRaw_positive_mean_zero (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in Ioi 0, sourceRaw coordinate x) = 0 := by
  have fullZero : (∫ x : ℝ, sourceRaw coordinate x) = 0 := by
    rw [sourceRaw, integral_indicator (measurableSet_symmetricInterval q),
      ← integral_congr_ae (burnolRieszSingleFourierSource_ae_raw coordinate)]
    have original := Constructor.mean_zero (burnolRieszSingleFourierSource coordinate)
    rw [Constructor.mean_integral] at original
    exact (mul_eq_zero.mp original).resolve_left (by norm_num)
  have negative : (∫ x : ℝ in Iic 0, sourceRaw coordinate x) =
      ∫ x : ℝ in Ioi 0, sourceRaw coordinate x := by
    calc
      _ = ∫ x : ℝ in Iic 0, sourceRaw coordinate (-x) :=
        setIntegral_congr_fun measurableSet_Iic (fun x _ => (sourceRaw_even coordinate x).symm)
      _ = _ := by simpa only [neg_zero] using integral_comp_neg_Iic 0 (sourceRaw coordinate)
  have split := setIntegral_union (Iic_disjoint_Ioi (a := (0 : ℝ)) le_rfl) measurableSet_Ioi
    (sourceRaw_integrable coordinate).integrableOn (sourceRaw_integrable coordinate).integrableOn
  rw [Iic_union_Ioi, setIntegral_univ, fullZero, negative] at split
  linear_combination -(1 / 2 : ℂ) * split

private theorem tate_mean (raw : ℝ → ℂ) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)⁻¹ * burnolTateReciprocalRaw raw x) =
      ∫ x : ℝ in Ioi 0, raw x := by
  calc
    _ = ∫ x : ℝ in Ioi 0, (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • raw (x ^ (-1 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x positive
      have xpos : 0 < x := positive
      simp only [burnolTateReciprocalRaw, abs_of_pos xpos, abs_neg, abs_one, one_mul,
        Real.rpow_neg_one, Complex.real_smul]
      rw [show ((-1 : ℝ) - 1) = -2 by norm_num, Real.rpow_neg xpos.le, Real.rpow_two]
      push_cast
      ring
    _ = _ := integral_comp_rpow_Ioi raw (by norm_num)

private theorem tate_gap (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (small : |x| ≤ q) : burnolTateReciprocalRaw (sourceRaw coordinate) x = 0 := by
  by_cases zero : x = 0
  · simp [burnolTateReciprocalRaw, zero]
  have large : (4 : ℝ) ≤ |x⁻¹| := by
    rw [abs_inv]
    exact (le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) (abs_pos.mpr zero)).mpr (by simpa using small)
  have outside : x⁻¹ ∉ symmetricInterval q := fun inside => by linarith [abs_le.mpr inside]
  rw [burnolTateReciprocalRaw, sourceRaw, indicator_of_notMem outside, mul_zero]

/-- Fourier's q-slot is generated by the actual Tate source and its original mean. -/
theorem original_fourier_gap (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (fourierL2 (AmbientCounting.value coordinate)) = 0 := by
  let source := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let dual := burnolTateReciprocalL2 source
  let value := fourierL2 (AmbientCounting.value coordinate)
  have rawMem : MemLp (sourceRaw coordinate) 2 volume :=
    (Lp.memLp source).ae_eq (sourceRaw_read coordinate)
  have dualRead : (dual : ℝ → ℂ) =ᵐ[volume] burnolTateReciprocalRaw (sourceRaw coordinate) :=
    (burnolTateReciprocalL2_coeFn source).trans
      (burnolTateReciprocalRaw_ae_congr (Lp.memLp source) rawMem (sourceRaw_read coordinate))
  have dualEven : reflectL2 dual = dual := burnolReflectL2_eq_of_even_raw dual _ dualRead (fun x => by
    simp only [burnolTateReciprocalRaw, abs_neg, inv_neg, sourceRaw_even])
  have dualGap : (dual : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae dualRead,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
    rw [read, tate_gap coordinate (abs_le.mpr inside)]
  have realizes (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead dual test =
      ∫ x : ℝ, test x * value x := by
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      burnolRemainderRealization_fourier source (AmbientCounting.value coordinate)
        (original_realizes coordinate) test
  obtain ⟨raw, rawRep, rawGap, valueRep⟩ :=
    burnolRemainderSourceRead_realization_ae dual value dualEven dualGap realizes
  have same := rawRep.symm.trans dualRead
  have meanZero : (∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) = 0 := by
    calc
      _ = ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * burnolTateReciprocalRaw (sourceRaw coordinate) u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae same] with u read
        rw [read]
      _ = _ := (tate_mean (sourceRaw coordinate)).trans (sourceRaw_positive_mean_zero coordinate)
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
    ae_restrict_of_ae valueRep, ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval q))] with x restricted read inside zeroAt
  change burnolQuarterRestriction value x = _ at restricted
  change burnolQuarterRestriction value x = (0 : BurnolQuarterIntervalL2) x
  rw [restricted, read, meanZero, sub_zero, burnolInnerGapForward_innerGap raw rawGap (abs_le.mpr inside), zeroAt]
  rfl

end
end OriginalRieszFinitePairing.CoPoisson.Ward.AmbientFourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
