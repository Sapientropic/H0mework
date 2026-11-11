import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactC1
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
open scoped Topology InnerProductSpace
open private even_half_integral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
open private fourier_raw_even_of_fixed from
  H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local instance finiteQuarter : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def compactReverseSeedRaw (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  if |x| ≤ q then raw |x| else 0

def compactReverseFiniteRaw (raw : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, compactReverseSeedRaw raw ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), compactReverseSeedRaw raw (a * x)

def compactReverseFloorRaw (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ DualSourceRaw.channels x, raw ((n : ℝ) * |x|)

private theorem compact_seed_measurable (raw : ℝ → ℂ) (measured : Measurable raw) :
    Measurable (compactReverseSeedRaw raw) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (measured.comp continuous_abs.measurable) measurable_const

private theorem compact_seed_read (state : Hq) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x) :
    (E state : ℝ → ℂ) =ᵐ[volume] compactReverseSeedRaw raw := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp represents
  filter_upwards [burnolQuarterZeroExtension_coe state, localRead] with x extended actual
  rw [extended]
  by_cases inside : |x| ≤ q
  · have member : x ∈ symmetricInterval q := abs_le.mp inside
    rw [compactReverseSeedRaw, if_pos inside, indicator_of_mem member,
      actual member, even x member]
  · have outside : x ∉ symmetricInterval q := fun member => inside (abs_le.mpr member)
    rw [compactReverseSeedRaw, if_neg inside, indicator_of_notMem outside]

/-- Both finite channels are read at the same N on the entire original compact source. -/
theorem actual_compact_reverse_finite_raw (state : Hq) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x)
    (measured : Measurable raw) (N : ℕ) :
    (DualSource.source N (E state) : ℝ → ℂ) =ᵐ[volume] compactReverseFiniteRaw raw N := by
  let seed := E state
  have seedRead := compact_seed_read state raw represents even
  have integralRead :
      ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
        fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), compactReverseSeedRaw raw (a * x) := by
    apply source_l2_bochner_coeFn (volume.restrict (Ioc 0 (N : ℝ))) _
      (ContinuousChannels.channel_integrable 1 N seed)
      (fun point : ℝ × ℝ => compactReverseSeedRaw raw (point.1 * point.2))
      ((compact_seed_measurable raw measured).comp (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    exact DualSourceRaw.channel_coeFn seed _ seedRead a inside.1
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n : ℝ) seed x = compactReverseSeedRaw raw ((n : ℝ) * x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn seed _ seedRead (n : ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.2).1)
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed)
      (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel 1 (n : ℝ) seed),
    integralRead, channels] with x subtraction sumRead normalization channelAt
  change ((∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) x = _
  rw [subtraction, Pi.sub_apply, sumRead, normalization, compactReverseFiniteRaw]
  congr 1
  apply Finset.sum_congr rfl
  intro n member
  exact channelAt ⟨n, member⟩

private theorem compact_half_mean_zero (state : M) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x) :
    (∫ x : ℝ in Ioc 0 q, raw x) = 0 := by
  have absoluteRead : (state : ℝ → ℂ) =ᵐ[μq] fun x => raw |x| := by
    filter_upwards [represents, ae_restrict_mem (measurableSet_symmetricInterval q)] with x actual inside
    exact actual.trans (even x inside).symm
  have domain : Integrable (fun x => raw |x|) μq :=
    ((Lp.memLp (state : Hq)).integrable (by norm_num)).congr absoluteRead
  have mean := Constructor.mean_zero state
  rw [Constructor.mean_integral, integral_congr_ae absoluteRead,
    even_half_integral _ domain (fun x => by rw [abs_neg])] at mean
  have halfRead : (∫ x : ℝ in Ioc 0 q, raw |x|) = ∫ x : ℝ in Ioc 0 q, raw x :=
    setIntegral_congr_fun measurableSet_Ioc (fun x inside => by rw [abs_of_pos inside.1])
  rw [halfRead] at mean
  linear_combination mean / 4

private theorem compact_normalization_zero (state : M) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x)
    (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) (covered : q ≤ (N : ℝ) * |x|) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), compactReverseSeedRaw raw (a * x)) = 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have parity (a : ℝ) (positive : 0 < a) :
      compactReverseSeedRaw raw (a * x) = compactReverseSeedRaw raw (a * |x|) := by
    simp only [compactReverseSeedRaw, abs_mul, abs_of_pos positive, abs_abs]
  have scaled : (∫ a : ℝ in Ioc 0 (N : ℝ), compactReverseSeedRaw raw (a * x)) =
      |x|⁻¹ • ∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), compactReverseSeedRaw raw t := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => parity a inside.1),
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ absolute.ne', zero_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ) * |x|)]
  have intervalRead : (∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), compactReverseSeedRaw raw t) =
      ∫ t : ℝ in Ioc 0 q, raw t := by
    have pointwise : EqOn (compactReverseSeedRaw raw) ((Ioc 0 q).indicator raw)
        (Ioc 0 ((N : ℝ) * |x|)) := by
      intro t inside
      simp only [compactReverseSeedRaw, abs_of_pos inside.1, indicator_apply, mem_Ioc, inside.1, true_and]
    rw [setIntegral_congr_fun measurableSet_Ioc pointwise, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc le_rfl covered)]
  rw [scaled, intervalRead, compact_half_mean_zero state raw represents even, smul_zero]

private theorem compact_seed_channel (raw : ℝ → ℂ) (x : ℝ) (nonzero : x ≠ 0)
    (n : ℕ) (positive : 0 < n) :
    compactReverseSeedRaw raw ((n : ℝ) * x) =
      if n ∈ DualSourceRaw.channels x then raw ((n : ℝ) * |x|) else 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have incidence : (n : ℝ) * |x| ≤ q ↔ n ∈ DualSourceRaw.channels x := by
    simp only [DualSourceRaw.channels, Finset.mem_Icc, show 1 ≤ n from positive, true_and,
      Nat.le_floor_iff' positive.ne', le_div_iff₀ absolute]
  simp only [compactReverseSeedRaw, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), incidence]

private theorem compact_finite_event (state : M) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x)
    (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) (complete : q / |x| < (N : ℝ)) :
    compactReverseFiniteRaw raw N x = compactReverseFloorRaw raw x := by
  classical
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have subset : DualSourceRaw.channels x ⊆ Finset.Ico 1 N := by
    intro n inside
    have members := Finset.mem_Icc.mp inside
    have bounded : (n : ℝ) ≤ q / |x| := (Nat.le_floor_iff' (by omega : n ≠ 0)).mp members.2
    exact Finset.mem_Ico.mpr ⟨members.1, by exact_mod_cast bounded.trans_lt complete⟩
  rw [compactReverseFiniteRaw,
    compact_normalization_zero state raw represents even N x nonzero ((div_lt_iff₀ absolute).mp complete).le,
    sub_zero]
  calc
    _ = ∑ n ∈ Finset.Ico 1 N, if n ∈ DualSourceRaw.channels x then raw ((n : ℝ) * |x|) else 0 := by
      apply Finset.sum_congr rfl
      intro n inside
      exact compact_seed_channel raw x nonzero n (Finset.mem_Ico.mp inside).1
    _ = _ := by
      rw [← Finset.sum_filter]
      unfold compactReverseFloorRaw
      congr 1
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun member => member.2, fun member => ⟨subset member, member⟩⟩

private theorem compact_strong_floor (state : M) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x) (measured : Measurable raw)
    (value : BurnolL2)
    (graph : Tendsto (fun N : ℕ => DualSource.source N (E (state : Hq))) atTop (𝓝 value)) :
    (value : ℝ → ℂ) =ᵐ[volume] compactReverseFloorRaw raw := by
  obtain ⟨indices, strict, pointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp graph).exists_seq_tendsto_ae
  have reads : ∀ᵐ x : ℝ ∂volume, ∀ N : ℕ,
      DualSource.source N (E (state : Hq)) x = compactReverseFiniteRaw raw N x :=
    ae_all_iff.mpr (fun N => actual_compact_reverse_finite_raw (state : Hq) raw represents even measured N)
  filter_upwards [pointwise, reads, volume.ae_ne (0 : ℝ)] with x converges read nonzero
  have event : ∀ᶠ N : ℕ in atTop, compactReverseFiniteRaw raw N x = compactReverseFloorRaw raw x := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (q / |x|))]
      with N complete
    exact compact_finite_event state raw represents even N x nonzero complete
  have finiteLimit : Tendsto (fun N : ℕ => compactReverseFiniteRaw raw N x) atTop
      (𝓝 (compactReverseFloorRaw raw x)) := tendsto_const_nhds.congr' (by
    filter_upwards [event] with N actual
    exact actual.symm)
  have actual := finiteLimit.comp strict.tendsto_atTop
  have same := converges.congr' (Eventually.of_forall (fun n => read (indices n)))
  exact tendsto_nhds_unique same actual

/-- The generated compact C1 reverse graph has the complete finite-floor field, with its source mean paid. -/
theorem actual_compact_c1_reverse_floor (state : M) (raw slope : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x)
    (measured : Measurable raw) (valueContinuous : ContinuousOn raw (Icc (0 : ℝ) q))
    (slopeContinuous : ContinuousOn slope (Icc (0 : ℝ) q))
    (derivative : ∀ x : ℝ, 0 < x → x ≤ q → HasDerivAt raw (slope x) x) :
    (poissonPair (InfiniteWeightedProgram.program (deriv (weight raw)) burnolUnitCountingPrimitiveL2) : ℝ → ℂ) =ᵐ[volume]
      compactReverseFloorRaw raw := by
  obtain ⟨weightDerivative, actualSlopeContinuous, _measuredWeight, domain, head⟩ :=
    actual_compact_c1_inputs (state : Hq) raw slope represents even measured valueContinuous slopeContinuous derivative
  exact compact_strong_floor state raw represents even measured _
    (actual_compact_reverse (state : Hq) raw represents even weightDerivative actualSlopeContinuous domain head)

/-- The original S(log B0) source generates this full floor field before any endpoint or K read. -/
theorem actual_log_return_count_field (c : BurnolCompletedMellinCoordinate) :
    (poissonPair (logProgramme c) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ DualSourceRaw.channels x,
        burnolMeanZeroFourierRaw (logBFirst c 0) ((n : ℝ) * |x|) := by
  have smooth := OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative.actual_return_contDiff (logBFirst c 0)
  have fixed : reflectRestricted q (logBFirst c 0 : Hq) = (logBFirst c 0 : Hq) :=
    congrArg (fun state : M => (state : Hq)) (log_B_even c 0)
  apply compact_strong_floor (S (logBFirst c 0)) _
    (burnolMeanZeroFourier_ae_raw (logBFirst c 0)) _ smooth.continuous.measurable _
    (actual_log_return_reverse c)
  intro x _
  by_cases positive : 0 ≤ x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive)]
    simp only [burnolMeanZeroFourierRaw, fourier_raw_even_of_fixed _ fixed x]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
