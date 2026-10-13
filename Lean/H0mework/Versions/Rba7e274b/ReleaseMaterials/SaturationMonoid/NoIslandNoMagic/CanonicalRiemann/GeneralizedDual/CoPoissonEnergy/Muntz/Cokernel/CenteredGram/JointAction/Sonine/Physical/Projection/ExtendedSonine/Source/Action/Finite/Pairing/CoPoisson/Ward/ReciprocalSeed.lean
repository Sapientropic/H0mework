import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Normalization
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ReciprocalSeed

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalPaPhysicalGreen
noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem seed_eq_cutoff (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (large : 4 ≤ upper) :
    burnolWeightedReciprocalStepSource 4 upper (ReciprocalTail.weight coordinate)
        (deriv (ReciprocalTail.weight coordinate)) =
      burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) -
        originalPhysicalCutoff upper⁻¹
          (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  let original := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  have source := weighted_source_coeFn 4 upper (ReciprocalTail.weight coordinate)
    (deriv (ReciprocalTail.weight coordinate)) (by norm_num) large
    (fun u inside => (ReciprocalTail.weight_hasDerivAt coordinate u
      (lt_of_lt_of_le (by norm_num) inside.1)).differentiableAt.hasDerivAt)
    ((ReciprocalTail.weight_deriv_continuousOn coordinate).mono
      (fun _ inside => lt_of_lt_of_le (by norm_num) inside.1))
    (ReciprocalTail.weight_deriv_measurable coordinate)
  have originalRaw := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolRieszSingleFourierSource_ae_raw coordinate)
  apply Lp.ext
  filter_upwards [source, Lp.coeFn_sub original (originalPhysicalCutoff upper⁻¹ original),
    originalPhysicalCutoff_coeFn upper⁻¹ original,
    burnolQuarterZeroExtension_coe (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2),
    originalRaw, volume.ae_ne (0 : ℝ)] with x sourceAt subAt cutoffAt extendedAt rawAt nonzero
  change _ = (original - originalPhysicalCutoff upper⁻¹ original : BurnolL2) x
  rw [sourceAt, subAt]
  change _ = original x - originalPhysicalCutoff upper⁻¹ original x
  rw [cutoffAt]
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have positive : 0 < upper := lt_of_lt_of_le (by norm_num) large
  have lower : 4 ≤ |x|⁻¹ ↔ x ∈ symmetricInterval q := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) absolute]
    change |x| ≤ (4 : ℝ)⁻¹ ↔ -q ≤ x ∧ x ≤ q
    norm_num only [inv_eq_one_div]
    exact abs_le
  have beyond : |x|⁻¹ < upper ↔ x ∉ symmetricInterval upper⁻¹ := by
    rw [inv_lt_comm₀ absolute positive]
    exact lt_iff_not_ge.trans (not_congr abs_le)
  simp only [burnolReciprocalStepSourceRaw]
  by_cases small : x ∈ symmetricInterval upper⁻¹
  · rw [indicator_of_mem small, sub_self,
      if_neg (fun active => (beyond.mp active.2) small), mul_zero]
  · rw [indicator_of_notMem small, sub_zero]
    by_cases inside : x ∈ symmetricInterval q
    · rw [if_pos ⟨lower.mpr inside, beyond.mpr small⟩]
      change _ = (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) x
      rw [extendedAt, indicator_of_mem inside, rawAt inside]
      have even : burnolRieszSingleFourierSourceRaw coordinate |x| =
          burnolRieszSingleFourierSourceRaw coordinate x := by
        rcases le_total 0 x with nonnegative | nonpositive
        · rw [abs_of_nonneg nonnegative]
        · rw [abs_of_nonpos nonpositive, OriginalRieszFinitePairing.source_raw_even]
      simp only [ReciprocalTail.weight, inv_inv, Complex.ofReal_inv, div_eq_mul_inv]
      rw [mul_inv_cancel_right₀ (Complex.ofReal_ne_zero.mpr absolute.ne'), even]
    · rw [if_neg (fun active => inside (lower.mp active.1)), mul_zero]
      change _ = (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) x
      rw [extendedAt, indicator_of_notMem inside]

private theorem small_cutoff_tendsto (value : BurnolL2) :
    Tendsto (fun upper : ℝ => originalPhysicalCutoff upper⁻¹ value) atTop (𝓝 0) := by
  let raw := fun upper : ℝ => (symmetricInterval upper⁻¹).indicator (value : ℝ → ℂ)
  have member (upper : ℝ) : MemLp (raw upper) 2 volume :=
    (Lp.memLp value).indicator (measurableSet_symmetricInterval _)
  have rawLimit : ∀ᵐ x : ℝ ∂volume, Tendsto (fun upper : ℝ => raw upper x) atTop (𝓝 0) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop |x|⁻¹] with upper large
    have positive : 0 < upper := (inv_pos.mpr (abs_pos.mpr nonzero)).trans large
    have outside : x ∉ symmetricInterval upper⁻¹ := by
      intro inside
      exact (not_le_of_gt ((inv_lt_comm₀ positive (abs_pos.mpr nonzero)).mpr large)) (abs_le.mpr inside)
    simp only [raw, indicator_of_notMem outside]
  have squareLimit : Tendsto (fun upper : ℝ => ∫ x : ℝ, ‖raw upper x‖ ^ 2) atTop (𝓝 0) := by
    have result := tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => ‖value x‖ ^ 2)
      (F := fun upper x => ‖raw upper x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (Eventually.of_forall (fun upper => (member upper).norm.integrable_sq.aestronglyMeasurable))
      (Eventually.of_forall (fun upper => by
        filter_upwards with x
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        by_cases inside : x ∈ symmetricInterval upper⁻¹
        · simp only [raw, indicator_of_mem inside]
          exact le_rfl
        · simp only [raw, indicator_of_notMem inside, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
          exact sq_nonneg _))
      (Lp.memLp value).norm.integrable_sq
      (rawLimit.mono (fun x limit => by simpa using limit.norm.pow 2))
    simpa using result
  have eLpLimit : Tendsto (fun upper : ℝ => eLpNorm (raw upper - (0 : ℝ → ℂ)) 2 volume) atTop (𝓝 0) := by
    have realLimit := squareLimit.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
    have result := ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using realLimit)
    convert! result using 1
    · funext upper
      rw [sub_zero, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (member upper)]
      simp
    · simp
  have actual := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' raw member (0 : ℝ → ℂ) MemLp.zero).mpr eLpLimit
  simp only [MemLp.toLp_zero] at actual
  apply actual.congr'
  filter_upwards with upper
  apply Lp.ext
  exact (member upper).coeFn_toLp.trans (originalPhysicalCutoff_coeFn upper⁻¹ value).symm

theorem seed_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun upper : ℝ => burnolWeightedReciprocalStepSource 4 upper
      (ReciprocalTail.weight coordinate) (deriv (ReciprocalTail.weight coordinate))) atTop
      (𝓝 (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) := by
  have actual := (tendsto_const_nhds (x := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))).sub (small_cutoff_tendsto
    (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))
  simp only [sub_zero] at actual
  apply actual.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper large
  exact (seed_eq_cutoff coordinate upper large).symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ReciprocalSeed
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
