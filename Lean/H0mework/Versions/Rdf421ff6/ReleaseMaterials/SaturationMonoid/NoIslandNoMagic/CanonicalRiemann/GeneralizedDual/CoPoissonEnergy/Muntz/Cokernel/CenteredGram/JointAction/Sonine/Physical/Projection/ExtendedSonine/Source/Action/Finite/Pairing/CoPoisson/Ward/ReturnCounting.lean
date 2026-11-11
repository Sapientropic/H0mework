import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCounting
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.TrapezoidSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ReturnCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension

private theorem half_integral_zero (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in Ioc 0 q, burnolRieszReturnRaw coordinate x) = 0 := by
  have reflected := intervalIntegral.integral_comp_neg
    (f := burnolRieszReturnRaw coordinate) (a := -q) (b := 0)
  simp only [return_raw_even, neg_zero, neg_neg] at reflected
  have left := (burnolRieszReturnRaw_continuous coordinate).intervalIntegrable (μ := volume) (-q) 0
  have right := (burnolRieszReturnRaw_continuous coordinate).intervalIntegrable (μ := volume) 0 q
  have whole := intervalIntegral.integral_add_adjacent_intervals left right
  rw [reflected, Constructor.return_integral_zero] at whole
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)]
  linear_combination whole / 2

def seedRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x| ≤ q then burnolRieszReturnRaw coordinate |x| else 0

def raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)

def eventRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n ∈ DualSourceRaw.channels x, burnolRieszReturnRaw coordinate ((n : ℝ) * |x|)

def finite (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  DualSource.source N (burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2))

theorem seed_measurable (coordinate : BurnolCompletedMellinCoordinate) : Measurable (seedRaw coordinate) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    ((burnolRieszReturnRaw_continuous coordinate).comp continuous_abs).measurable measurable_const

theorem seed_read (coordinate : BurnolCompletedMellinCoordinate) : (burnolQuarterZeroExtension
    (Constructor.returnState coordinate : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[volume] seedRaw coordinate := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (Constructor.returnState_read coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe (Constructor.returnState coordinate : BurnolQuarterIntervalL2), localRead]
    with x extension read
  rw [extension]
  by_cases inside : |x| ≤ q
  · rw [seedRaw, if_pos inside, indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside),
      read (abs_le.mp inside)]
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, return_raw_even coordinate x]
  · rw [seedRaw, if_neg inside,
      indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h))]

theorem raw_measurable (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : StronglyMeasurable (raw coordinate N) := by
  have kernel : StronglyMeasurable (fun p : ℝ × ℝ => seedRaw coordinate (p.1 * p.2)) :=
    ((seed_measurable coordinate).comp (by fun_prop)).stronglyMeasurable
  have integralRead : StronglyMeasurable (fun x : ℝ => ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) :=
    kernel.integral_prod_left'
  apply StronglyMeasurable.sub _ integralRead
  apply Finset.stronglyMeasurable_fun_sum
  intro n _
  exact ((seed_measurable coordinate).comp (by fun_prop)).stronglyMeasurable

private theorem normalization_coeFn (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a
      (burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x) := by
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc 0 (N : ℝ))) _ (ContinuousChannels.channel_integrable 1 (N : ℝ) _)
    (fun p : ℝ × ℝ => seedRaw coordinate (p.1 * p.2)) ((seed_measurable coordinate).comp (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  exact DualSourceRaw.channel_coeFn _ _ (seed_read coordinate) a inside.1

theorem finite_coeFn (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : (finite coordinate N : ℝ → ℂ) =ᵐ[volume] raw coordinate N := by
  let seed := burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n : ℝ) seed x = seedRaw coordinate ((n : ℝ) * x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn seed _ (seed_read coordinate) (n : ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.2).1)
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed)
    (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel 1 (n : ℝ) seed),
    normalization_coeFn coordinate N, channels] with x difference sum integral channel
  change ((∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) x = _
  rw [difference, Pi.sub_apply, sum, integral]
  unfold raw
  congr 1
  apply Finset.sum_congr rfl
  intro n inside
  exact channel ⟨n, inside⟩

theorem finite_mean (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (finite coordinate N)) =
      2 * inner ℂ SmallScaleLog.logL2 (Constructor.returnState coordinate : BurnolQuarterIntervalL2) := by
  let b := Constructor.returnState coordinate
  have first : inner ℂ (intervalConstant q) (burnolQuarterRestriction (finite coordinate N)) =
      inner ℂ (WindowCounting.windowSource N (intervalConstant q)) (b : BurnolQuarterIntervalL2) := by
    calc
      _ = inner ℂ (burnolQuarterZeroExtension (intervalConstant q)) (finite coordinate N) :=
        (ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _).symm
      _ = inner ℂ (FiniteForcing.source N (burnolQuarterZeroExtension (intervalConstant q)))
          (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2)) := (CountingDual.source_pairing N _ _).symm
      _ = _ := ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
  have meanZero : inner ℂ (intervalConstant q) (b : BurnolQuarterIntervalL2) = 0 :=
    (Submodule.mem_orthogonal _ _).mp b.property _ (Submodule.mem_span_singleton_self _)
  unfold burnolQuarterMeanCoefficient
  rw [first, WindowCounting.constant_source N positive, inner_add_left, inner_smul_left,
    meanZero, mul_zero, zero_add, Complex.ofReal_pow,
    burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  norm_num
  ring

/-- The full continuous channel vanishes only after the actual mean-zero source interval is covered. -/
theorem continuous_raw_zero (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (covered : q ≤ (N : ℝ) * |x|) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) = 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have even (a : ℝ) (positive : 0 < a) : seedRaw coordinate (a * x) = seedRaw coordinate (a * |x|) := by
    simp only [seedRaw, abs_mul, abs_of_pos positive, abs_abs]
  have scaled : (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) =
      |x|⁻¹ • ∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), seedRaw coordinate t := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => even a inside.1),
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ absolute.ne', zero_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ) * |x|)]
  have intervalRead : (∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), seedRaw coordinate t) =
      ∫ t : ℝ in Ioc 0 q, burnolRieszReturnRaw coordinate t := by
    have pointwise : EqOn (seedRaw coordinate) ((Ioc 0 q).indicator (burnolRieszReturnRaw coordinate))
        (Ioc 0 ((N : ℝ) * |x|)) := by
      intro t inside
      simp only [seedRaw, abs_of_pos inside.1, indicator_apply, mem_Ioc, inside.1, true_and]
    rw [setIntegral_congr_fun measurableSet_Ioc pointwise, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc le_rfl covered)]
  rw [scaled, intervalRead, half_integral_zero, smul_zero]

theorem seed_channel (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0)
    (n : ℕ) (positive : 0 < n) :
    seedRaw coordinate ((n : ℝ) * x) =
      if n ∈ DualSourceRaw.channels x then burnolRieszReturnRaw coordinate ((n : ℝ) * |x|) else 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have incidence : (n : ℝ) * |x| ≤ q ↔ n ∈ DualSourceRaw.channels x := by
    simp only [DualSourceRaw.channels, Finset.mem_Icc, show 1 ≤ n from positive, true_and,
      Nat.le_floor_iff' positive.ne', le_div_iff₀ absolute]
  simp only [seedRaw, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), incidence]

theorem raw_event (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (complete : q / |x| < (N : ℝ)) : raw coordinate N x = eventRaw coordinate x := by
  classical
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have subset : DualSourceRaw.channels x ⊆ Finset.Ico 1 N := by
    intro n inside
    have members := Finset.mem_Icc.mp inside
    have bounded : (n : ℝ) ≤ q / |x| := (Nat.le_floor_iff' (by omega : n ≠ 0)).mp members.2
    exact Finset.mem_Ico.mpr ⟨members.1, by exact_mod_cast bounded.trans_lt complete⟩
  rw [raw, continuous_raw_zero coordinate N x nonzero ((div_lt_iff₀ absolute).mp complete).le, sub_zero]
  calc
    _ = ∑ n ∈ Finset.Ico 1 N, if n ∈ DualSourceRaw.channels x then
        burnolRieszReturnRaw coordinate ((n : ℝ) * |x|) else 0 := by
      apply Finset.sum_congr rfl
      intro n inside
      exact seed_channel coordinate x nonzero n (Finset.mem_Ico.mp inside).1
    _ = _ := by
      rw [← Finset.sum_filter]
      unfold eventRaw
      congr 1
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun member => member.2, fun member => ⟨subset member, member⟩⟩

theorem raw_eventually (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0) :
    ∀ᶠ N : ℕ in atTop, raw coordinate N x = eventRaw coordinate x := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (q / |x|))] with N complete
  exact raw_event coordinate N x nonzero complete

theorem event_aestronglyMeasurable (coordinate : BurnolCompletedMellinCoordinate) :
    AEStronglyMeasurable (eventRaw coordinate) volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun N => (raw_measurable coordinate N).aestronglyMeasurable)
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  apply tendsto_const_nhds.congr'
  filter_upwards [raw_eventually coordinate x nonzero] with N read
  exact read.symm

theorem event_outside (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (outside : q < |x|) :
    eventRaw coordinate x = 0 := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have index : ⌊q / |x|⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one absolute).mpr outside)
  rw [eventRaw, DualSourceRaw.channels, index]
  simp

def bound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  4 * PositionCounting.returnSlopeBound coordinate * q + PositionCounting.returnBound coordinate

theorem bound_nonnegative (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ bound coordinate := by
  unfold bound
  positivity [PositionCounting.return_slope_nonnegative coordinate, PositionCounting.return_bound_nonnegative coordinate]

theorem event_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    ‖eventRaw coordinate x‖ ≤ bound coordinate := by
  by_cases zero : x = 0
  · subst x
    simp only [eventRaw, DualSourceRaw.channels, abs_zero, div_zero, Nat.floor_zero,
      Finset.Icc_eq_empty_of_lt (by decide : 0 < 1), Finset.sum_empty, norm_zero]
    exact bound_nonnegative coordinate
  have original := PositionCounting.return_quadrature coordinate |x| (abs_pos.mpr zero)
  have mean := half_integral_zero coordinate
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)] at mean
  rw [mean, mul_zero, sub_zero] at original
  have increased : PositionCounting.returnSlopeBound coordinate * q + PositionCounting.returnBound coordinate ≤
      bound coordinate := by unfold bound; nlinarith [PositionCounting.return_slope_nonnegative coordinate]
  exact original.trans increased

private theorem partial_quadrature (coordinate : BurnolCompletedMellinCoordinate)
    (N : ℕ) (indexPositive : 0 < N) (x : ℝ) (positive : 0 < x) (inside : (N : ℝ) * x ≤ q) :
    ‖(∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t‖ ≤ bound coordinate := by
  have slope := PositionCounting.return_slope_nonnegative coordinate
  have grid := TrapezoidSource.grid_bound (burnolRieszReturnRaw coordinate)
    (burnolRieszReturnRawDerivative coordinate) (burnolRieszReturnRaw_continuous coordinate).continuousOn
    (fun t _ => burnolRieszReturnRaw_hasDerivAt coordinate t) x
    (2 * PositionCounting.returnSlopeBound coordinate) positive (by positivity) N inside
    (fun a ha b hb _ => (norm_sub_le _ _).trans ((add_le_add
      (PositionCounting.return_slope_bound coordinate b hb)
      (PositionCounting.return_slope_bound coordinate a ha)).trans_eq (by ring)))
  have endpoint : ‖(burnolRieszReturnRaw coordinate ((N : ℝ) * x) + burnolRieszReturnRaw coordinate 0) / 2‖ ≤
      PositionCounting.returnBound coordinate := by
    rw [norm_div, norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact (norm_add_le _ _).trans ((add_le_add
      (PositionCounting.return_bound coordinate ((N : ℝ) * x) ⟨by positivity, inside⟩)
      (PositionCounting.return_bound coordinate 0 (by norm_num))).trans_eq (by ring))
  have identity : (∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t =
      TrapezoidSource.grid (burnolRieszReturnRaw coordinate) x N -
        (burnolRieszReturnRaw coordinate ((N : ℝ) * x) + burnolRieszReturnRaw coordinate 0) / 2 := by
    have indices := Finset.sum_Ico_add_eq_sum_Icc (f := fun n : ℕ => burnolRieszReturnRaw coordinate ((n : ℝ) * x))
      (Nat.one_le_iff_ne_zero.mpr indexPositive.ne')
    unfold TrapezoidSource.grid
    rw [← indices]
    ring
  rw [identity]
  exact (norm_sub_le _ _).trans ((add_le_add grid endpoint).trans_eq (by unfold bound; ring))

private theorem partial_raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) (positive : 0 < x)
    (inside : (N : ℝ) * x ≤ q) : raw coordinate N x =
    (∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t := by
  have seed (a : ℝ) (ha : 0 < a) (haN : a ≤ N) : seedRaw coordinate (a * x) = burnolRieszReturnRaw coordinate (a * x) := by
    rw [seedRaw, abs_of_pos (mul_pos ha positive), if_pos ((mul_le_mul_of_nonneg_right haN positive.le).trans inside)]
  have channels : (∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * x)) =
      ∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact seed n (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
      (by exact_mod_cast (Finset.mem_Ico.mp hn).2.le)
  unfold raw
  rw [channels, setIntegral_congr_fun measurableSet_Ioc (fun a located => seed a located.1 located.2),
    ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
    intervalIntegral.integral_comp_mul_right _ positive.ne', zero_mul, Complex.real_smul, ofReal_inv]

theorem raw_bound (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (indexPositive : 0 < N)
    (x : ℝ) (nonzero : x ≠ 0) : ‖raw coordinate N x‖ ≤ bound coordinate := by
  have absolute : raw coordinate N x = raw coordinate N |x| := by
    simp only [raw, seedRaw, abs_mul, abs_abs]
  have positive := abs_pos.mpr nonzero
  by_cases covered : q < (N : ℝ) * |x|
  · rw [raw_event coordinate N x nonzero ((div_lt_iff₀ positive).mpr covered)]
    exact event_bound coordinate x
  · rw [absolute, partial_raw coordinate N |x| positive (le_of_not_gt covered)]
    exact partial_quadrature coordinate N indexPositive |x| positive (le_of_not_gt covered)

theorem raw_outside (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (indexPositive : 0 < N)
    (x : ℝ) (outside : q < |x|) : raw coordinate N x = 0 := by
  have positive : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have complete : q / |x| < (N : ℝ) := ((div_lt_one positive).mpr outside).trans_le
    (by exact_mod_cast indexPositive)
  rw [raw_event coordinate N x (abs_pos.mp positive) complete, event_outside coordinate x outside]

theorem event_memLp_two (coordinate : BurnolCompletedMellinCoordinate) : MemLp (eventRaw coordinate) 2 volume := by
  have dominant : MemLp ((symmetricInterval q).indicator (fun _ : ℝ => (bound coordinate : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval q) _ (Or.inr (by simp [symmetricInterval]))
  apply dominant.mono (event_aestronglyMeasurable coordinate)
  filter_upwards with x
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bound_nonnegative coordinate)]
    exact event_bound coordinate x
  · rw [indicator_of_notMem inside, event_outside coordinate x (lt_of_not_ge (fun small => inside (abs_le.mp small))), norm_zero]

def value (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (event_memLp_two coordinate).toLp (eventRaw coordinate)

theorem value_coeFn (coordinate : BurnolCompletedMellinCoordinate) : (value coordinate : ℝ → ℂ) =ᵐ[volume] eventRaw coordinate :=
  (event_memLp_two coordinate).coeFn_toLp

theorem value_support (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff q (value coordinate) = value coordinate := by
  apply OriginalRieszFiniteColumns.cutoff_eq_self_of_ae_zero
  filter_upwards [value_coeFn coordinate] with x read outside
  rw [read, event_outside coordinate x (lt_of_not_ge (fun small => outside (abs_le.mp small)))]


/-- The complete original finite dual source converges strongly; no limit or regularity is supplied by a caller. -/
theorem finite_tendsto (coordinate : BurnolCompletedMellinCoordinate) : Tendsto (finite coordinate) atTop (𝓝 (value coordinate)) := by
  let majorant : ℝ → ℝ := (symmetricInterval q).indicator (fun _ => (2 * bound coordinate) ^ 2)
  have integrable : Integrable majorant := by
    apply (integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr
    exact continuous_const.integrableOn_Icc
  have measured : ∀ᶠ N : ℕ in atTop, AEStronglyMeasurable
      (fun x : ℝ => ‖finite coordinate N x - eventRaw coordinate x‖ ^ 2) volume :=
    Eventually.of_forall (fun N => ((Lp.aestronglyMeasurable (finite coordinate N)).sub
      (event_aestronglyMeasurable coordinate)).norm.pow 2)
  have dominated : ∀ᶠ N : ℕ in atTop, ∀ᵐ x : ℝ ∂volume,
      ‖‖finite coordinate N x - eventRaw coordinate x‖ ^ 2‖ ≤ majorant x := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    filter_upwards [finite_coeFn coordinate N, volume.ae_ne (0 : ℝ)] with x read nonzero
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), read]
    dsimp only [majorant]
    by_cases inside : x ∈ symmetricInterval q
    · rw [indicator_of_mem inside]
      have difference : ‖raw coordinate N x - eventRaw coordinate x‖ ≤ 2 * bound coordinate :=
        (norm_sub_le _ _).trans ((add_le_add (raw_bound coordinate N positive x nonzero)
          (event_bound coordinate x)).trans_eq (by ring))
      exact pow_le_pow_left₀ (norm_nonneg _) difference 2
    · have outside : q < |x| := lt_of_not_ge (fun small => inside (abs_le.mp small))
      rw [indicator_of_notMem inside, raw_outside coordinate N positive x outside,
        event_outside coordinate x outside, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have reads : ∀ᵐ x : ℝ ∂volume, ∀ N : ℕ, finite coordinate N x = raw coordinate N x :=
    ae_all_iff.mpr (finite_coeFn coordinate)
  have pointwise : ∀ᵐ x : ℝ ∂volume, Tendsto
      (fun N : ℕ => ‖finite coordinate N x - eventRaw coordinate x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [reads, volume.ae_ne (0 : ℝ)] with x read nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [raw_eventually coordinate x nonzero] with N complete
    simp only [read N, complete, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have integralLimit := tendsto_integral_filter_of_dominated_convergence majorant measured dominated integrable pointwise
  simp only [integral_zero] at integralLimit
  have rootLimit := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp integralLimit
  simp only [Real.sqrt_zero] at rootLimit
  have normLimit := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp rootLimit
  simp only [ENNReal.ofReal_zero] at normLimit
  apply Lp.tendsto_Lp_of_tendsto_eLpNorm (eventRaw coordinate) (event_memLp_two coordinate)
  apply normLimit.congr'
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ((Lp.memLp (finite coordinate N)).sub (event_memLp_two coordinate))]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Pi.sub_apply, Real.sqrt_eq_rpow, one_div]

theorem value_mean (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (value coordinate)) =
      2 * inner ℂ SmallScaleLog.logL2 (Constructor.returnState coordinate : BurnolQuarterIntervalL2) := by
  have continuousMean : Continuous (fun value : BurnolL2 =>
      burnolQuarterMeanCoefficient (burnolQuarterRestriction value)) := by
    unfold burnolQuarterMeanCoefficient
    fun_prop
  have actual := (continuousMean.tendsto (value coordinate)).comp (finite_tendsto coordinate)
  have constantRead := actual.congr' (show _ =ᶠ[atTop]
      (fun _ : ℕ => 2 * inner ℂ SmallScaleLog.logL2 (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) from by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    exact finite_mean coordinate N positive)
  exact tendsto_nhds_unique constantRead tendsto_const_nhds

theorem original_support (coordinate : BurnolCompletedMellinCoordinate) :
    value coordinate = E (burnolQuarterRestriction (value coordinate)) := by
  have restricted := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (value coordinate))
  apply Lp.ext
  filter_upwards [value_coeFn coordinate,
    burnolQuarterZeroExtension_coe (burnolQuarterRestriction (value coordinate)), restricted]
      with x original extended localRead
  rw [extended]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside]
    exact (localRead inside).symm
  · rw [indicator_of_notMem inside, original]
    exact event_outside coordinate x (lt_of_not_ge (fun small => inside (abs_le.mp small)))

theorem value_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (value coordinate : ℝ → ℂ) := by
  rw [original_support coordinate]
  exact (burnolQuarterZeroExtensionRaw_integrable _).congr (burnolQuarterZeroExtension_coe _).symm

/-- The q mean coefficient is twice the full mass; neither is reset to zero by counting. -/
theorem value_integral (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ, value coordinate x) =
      inner ℂ SmallScaleLog.logL2 (Constructor.returnState coordinate : Hq) := by
  have mean := value_mean coordinate
  rw [Constructor.mean_integral] at mean
  have supported : (∫ x : ℝ, value coordinate x) =
      ∫ x : ℝ in symmetricInterval q, burnolQuarterRestriction (value coordinate) x := by
    conv_lhs => rw [original_support coordinate]
    rw [integral_congr_ae (burnolQuarterZeroExtension_coe _), integral_indicator (measurableSet_symmetricInterval q)]
  rw [supported]
  linear_combination mean / 2

/-- Same-N normality transfers the generated reverse Cauchy source to its forward direction. -/
theorem forward_cauchy (coordinate : BurnolCompletedMellinCoordinate) :
    CauchySeq (fun N : ℕ => FiniteForcing.source N (E (Constructor.returnState coordinate : Hq))) := by
  have actual := (finite_tendsto coordinate).cauchySeq
  rw [Metric.cauchySeq_iff] at actual ⊢
  intro epsilon positive
  obtain ⟨N, after⟩ := actual epsilon positive
  refine ⟨N, ?_⟩
  intro m hm n hn
  simpa only [dist_eq_norm, finite, CountingDual.difference_norm] using after m hm n hn

def forwardValue (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  limUnder atTop (fun N : ℕ => FiniteForcing.source N (E (Constructor.returnState coordinate : Hq)))

theorem forward_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (E (Constructor.returnState coordinate : Hq))) atTop
      (𝓝 (forwardValue coordinate)) := (forward_cauchy coordinate).tendsto_limUnder

theorem centered_reverse_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => CenteredCountingDual.reverse N (Constructor.returnState coordinate)) atTop
      (𝓝 (Constructor.zeroMean (burnolQuarterRestriction (value coordinate)))) :=
  Constructor.zeroMean.continuous.tendsto _ |>.comp
    (burnolQuarterRestriction.continuous.tendsto _ |>.comp (finite_tendsto coordinate))

theorem centered_forward_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => CenteredCountingDual.forward N (Constructor.returnState coordinate)) atTop
      (𝓝 (Constructor.zeroMean (burnolQuarterRestriction (forwardValue coordinate)))) :=
  Constructor.zeroMean.continuous.tendsto _ |>.comp
    (burnolQuarterRestriction.continuous.tendsto _ |>.comp (forward_tendsto coordinate))

theorem outside_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => CountingEnergy.outside N (Constructor.returnState coordinate)) atTop
      (𝓝 (forwardValue coordinate - E (burnolQuarterRestriction (forwardValue coordinate)))) :=
  (forward_tendsto coordinate).sub (burnolQuarterZeroExtension.continuous.tendsto _ |>.comp
    (burnolQuarterRestriction.continuous.tendsto _ |>.comp (forward_tendsto coordinate)))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ReturnCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
