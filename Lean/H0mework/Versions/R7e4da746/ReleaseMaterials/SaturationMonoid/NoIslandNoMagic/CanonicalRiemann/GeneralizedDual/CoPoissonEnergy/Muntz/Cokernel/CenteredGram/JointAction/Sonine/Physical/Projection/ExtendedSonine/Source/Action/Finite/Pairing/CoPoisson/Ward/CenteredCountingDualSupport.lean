import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CenteredCountingDualSupport

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "E" => burnolQuarterZeroExtension

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private def raw (state : BurnolQuarterIntervalL2) (x : ℝ) : ℂ :=
  (symmetricInterval q).indicator (fun y => (E state y + E state (-y)) / 2) x

private theorem raw_measurable (state : BurnolQuarterIntervalL2) : Measurable (raw state) :=
  ((((Lp.stronglyMeasurable (E state)).measurable.add
    ((Lp.stronglyMeasurable (E state)).measurable.comp measurable_neg)).div_const 2).indicator
      (measurableSet_symmetricInterval q))

private theorem raw_even (state : BurnolQuarterIntervalL2) (x : ℝ) : raw state (-x) = raw state x := by
  have located : -x ∈ symmetricInterval q ↔ x ∈ symmetricInterval q := by
    change -q ≤ -x ∧ -x ≤ q ↔ -q ≤ x ∧ x ≤ q
    constructor <;> rintro ⟨lower, upper⟩ <;> constructor <;> linarith
  unfold raw
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem (located.mpr inside), indicator_of_mem inside, neg_neg, add_comm]
  · rw [indicator_of_notMem (fun h => inside (located.mp h)), indicator_of_notMem inside]

private theorem raw_read (state : BurnolQuarterIntervalL2)
    (even : reflectRestricted q state = state) : (E state : ℝ → ℂ) =ᵐ[volume] raw state := by
  have reflected : reflectL2 (E state) = E state := by
    change reflectL2 (burnolRadiusZeroExtension q state) = _
    rw [burnolRadiusZeroExtension_reflect, even]
    rfl
  filter_upwards [burnolQuarterZeroExtension_coe state,
    Lp.coeFn_compMeasurePreserving (E state) negMeasurePreserving] with x extension reflection
  change reflectL2 (E state) x = E state (-x) at reflection
  rw [reflected] at reflection
  unfold raw
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, ← reflection]
    ring
  · rw [indicator_of_notMem inside, extension, indicator_of_notMem inside]

private theorem raw_local_read (state : BurnolQuarterIntervalL2)
    (even : reflectRestricted q state = state) : (state : ℝ → ℂ) =ᵐ[μq] raw state := by
  have restriction := LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (E state)
  change (burnolQuarterRestriction (E state) : ℝ → ℂ) =ᵐ[μq] _ at restriction
  rw [burnolQuarterRestriction_zeroExtension] at restriction
  exact restriction.trans (ae_restrict_of_ae (raw_read state even))

private theorem half_integral (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state : BurnolQuarterIntervalL2) = state) :
    (∫ x : ℝ in Ioc 0 q, raw (state : BurnolQuarterIntervalL2) x) = 0 := by
  let f := raw (state : BurnolQuarterIntervalL2)
  have integrable : IntegrableOn f (symmetricInterval q) :=
    ((Lp.memLp (state : BurnolQuarterIntervalL2)).integrable (by norm_num)).congr (raw_local_read _ even)
  have first : IntegrableOn f (Ioc (-q) 0) := integrable.mono_set (by
    intro x inside
    exact ⟨inside.1.le, inside.2.trans (by norm_num)⟩)
  have second : IntegrableOn f (Ioc 0 q) := integrable.mono_set (by
    intro x inside
    exact ⟨by linarith [inside.1], inside.2⟩)
  have split := setIntegral_union (Ioc_disjoint_Ioc_of_le (a := -q) (b := (0 : ℝ)) (c := 0) (d := q) le_rfl)
    measurableSet_Ioc first second
  rw [Ioc_union_Ioc_eq_Ioc (by norm_num : -q ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ q)] at split
  have reflected : (∫ x : ℝ in Ioc (-q) 0, f x) = ∫ x : ℝ in Ioc 0 q, f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : -q ≤ (0 : ℝ)),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)]
    have result := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := q)
    rw [show (fun x => f (-x)) = f from funext (raw_even _), neg_zero] at result
    exact result.symm
  have mean := Constructor.mean_zero state
  rw [Constructor.mean_integral, integral_congr_ae (raw_local_read _ even)] at mean
  change 2 * (∫ x : ℝ in Icc (-q) q, f x) = 0 at mean
  rw [integral_Icc_eq_integral_Ioc, split, reflected] at mean
  change (∫ x : ℝ in Ioc 0 q, f x) = 0
  linear_combination mean / 4

private theorem raw_abs (state : BurnolQuarterIntervalL2) (x : ℝ) : raw state x = raw state |x| := by
  rcases le_total 0 x with positive | negative
  · rw [abs_of_nonneg positive]
  · rw [abs_of_nonpos negative, raw_even]

private theorem normalization_outside (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state : BurnolQuarterIntervalL2) = state)
    (N : ℕ) (positive : 0 < N) (x : ℝ) (outside : q < |x|) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), raw (state : BurnolQuarterIntervalL2) (a * x)) = 0 := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have covered : q ≤ (N : ℝ) * |x| := outside.le.trans
    (by nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast positive])
  have scaled : (∫ a : ℝ in Ioc 0 (N : ℝ), raw (state : BurnolQuarterIntervalL2) (a * x)) =
      |x|⁻¹ • ∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), raw (state : BurnolQuarterIntervalL2) t := by
    have same (a : ℝ) (apos : 0 < a) : raw (state : BurnolQuarterIntervalL2) (a * x) =
        raw (state : BurnolQuarterIntervalL2) (a * |x|) := by
      rw [raw_abs _ (a * x), abs_mul, abs_of_pos apos]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => same a inside.1),
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ absolute.ne', zero_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ) * |x|)]
  have intervalRead : (∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), raw (state : BurnolQuarterIntervalL2) t) =
      ∫ t : ℝ in Ioc 0 q, raw (state : BurnolQuarterIntervalL2) t := by
    have pointwise : EqOn (raw (state : BurnolQuarterIntervalL2))
        ((Ioc 0 q).indicator (raw (state : BurnolQuarterIntervalL2))) (Ioc 0 ((N : ℝ) * |x|)) := by
      intro t inside
      by_cases small : t ≤ q
      · rw [indicator_of_mem (show t ∈ Ioc 0 q from ⟨inside.1, small⟩)]
      · rw [indicator_of_notMem (show t ∉ Ioc 0 q from fun h => small h.2), raw,
          indicator_of_notMem (show t ∉ symmetricInterval q from fun h => small h.2)]
    rw [setIntegral_congr_fun measurableSet_Ioc pointwise, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioc le_rfl covered)]
  rw [scaled, intervalRead, half_integral state even, smul_zero]

private theorem normalization_coeFn (state : BurnolQuarterIntervalL2)
    (even : reflectRestricted q state = state) (N : ℕ) :
    ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a (E state) : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), raw state (a * x) := by
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc 0 (N : ℝ))) _ (ContinuousChannels.channel_integrable 1 (N : ℝ) _)
    (fun p : ℝ × ℝ => raw state (p.1 * p.2)) ((raw_measurable state).comp (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  exact DualSourceRaw.channel_coeFn _ _ (raw_read state even) a inside.1

/-- The original mean-zero/even input pays the entire reverse-source support, including every small positive scale. -/
theorem source_support (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state : BurnolQuarterIntervalL2) = state)
    (N : ℕ) (positive : 0 < N) :
    DualSource.source N (E (state : BurnolQuarterIntervalL2)) =
      E (burnolQuarterRestriction (DualSource.source N (E (state : BurnolQuarterIntervalL2)))) := by
  let seed := E (state : BurnolQuarterIntervalL2)
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n : ℝ) seed x = raw (state : BurnolQuarterIntervalL2) ((n : ℝ) * x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn seed _ (raw_read _ even) (n : ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.2).1)
  symm
  apply OriginalRieszFiniteColumns.cutoff_eq_self_of_ae_zero
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed)
    (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel 1 (n : ℝ) seed),
    normalization_coeFn _ even N, channels] with x difference sum integral channel
  intro notInside
  have outside : q < |x| := lt_of_not_ge (fun h => notInside (abs_le.mp h))
  change ((∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) x = 0
  rw [difference, Pi.sub_apply, sum, integral, normalization_outside state even N positive x outside, sub_zero]
  apply Finset.sum_eq_zero
  intro n inside
  rw [channel ⟨n, inside⟩, raw]
  apply indicator_of_notMem
  intro member
  have large : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp inside).1
  have bound := abs_le.mpr member
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at bound
  nlinarith [abs_nonneg x]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.CenteredCountingDualSupport
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
