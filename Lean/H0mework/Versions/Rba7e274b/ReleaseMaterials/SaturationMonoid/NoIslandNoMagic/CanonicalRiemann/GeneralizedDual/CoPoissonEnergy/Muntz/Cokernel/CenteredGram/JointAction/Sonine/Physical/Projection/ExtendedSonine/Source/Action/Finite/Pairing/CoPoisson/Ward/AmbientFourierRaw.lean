import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientFourier

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.AmbientFourierRaw

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section

local notation "q" => (1 / 4 : ℝ)

/-- The actual Tate image of the original zero extension. -/
def reciprocalRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if 4 ≤ |x| then ReciprocalTail.weight coordinate |x| else 0

def channels (x : ℝ) : Finset ℕ := Finset.Icc 1 ⌊|x| / 4⌋₊

/-- Every channel samples the original b at its original reciprocal position. -/
def raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ)⁻¹ * ∑ n ∈ channels x, burnolRieszSingleFourierSourceRaw coordinate ((n : ℝ) / |x|)

private theorem source_abs (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszSingleFourierSourceRaw coordinate |x| = burnolRieszSingleFourierSourceRaw coordinate x := by
  rcases le_total 0 x with positive | negative
  · rw [abs_of_nonneg positive]
  · rw [abs_of_nonpos negative, OriginalRieszFinitePairing.source_raw_even]

theorem reciprocalRaw_original (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolTateReciprocalRaw ((symmetricInterval q).indicator
      (burnolRieszSingleFourierSourceRaw coordinate)) x = reciprocalRaw coordinate x := by
  by_cases zero : x = 0
  · simp [burnolTateReciprocalRaw, reciprocalRaw, zero]
  have positive : 0 < |x| := abs_pos.mpr zero
  have incidence : x⁻¹ ∈ symmetricInterval q ↔ 4 ≤ |x| := by
    change -q ≤ x⁻¹ ∧ x⁻¹ ≤ q ↔ 4 ≤ |x|
    rw [← abs_le, abs_inv, inv_le_comm₀ positive (by norm_num : (0 : ℝ) < q)]
    norm_num
  unfold burnolTateReciprocalRaw reciprocalRaw
  by_cases active : 4 ≤ |x|
  · rw [indicator_of_mem (incidence.mpr active), if_pos active]
    have even := source_abs coordinate x⁻¹
    rw [abs_inv] at even
    rw [← even, ReciprocalTail.weight]
    ring
  · rw [indicator_of_notMem (fun inside => active (incidence.mp inside)), if_neg active, mul_zero]

theorem reciprocalRaw_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) : ℝ → ℂ) =ᵐ[volume]
      reciprocalRaw coordinate := by
  let original := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let originalRaw := (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate)
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolRieszSingleFourierSource_ae_raw coordinate)
  have originalRead : (original : ℝ → ℂ) =ᵐ[volume] originalRaw := by
    filter_upwards [burnolQuarterZeroExtension_coe
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2), localRead] with x extendedAt rawAt
    rw [extendedAt]
    by_cases inside : x ∈ symmetricInterval q
    · simp only [originalRaw, indicator_of_mem inside, rawAt inside]
    · simp only [originalRaw, indicator_of_notMem inside]
  have tateRead := (burnolTateReciprocalL2_coeFn original).trans
    (burnolTateReciprocalRaw_ae_congr (Lp.memLp original) ((Lp.memLp original).ae_eq originalRead) originalRead)
  exact tateRead.trans (Eventually.of_forall (reciprocalRaw_original coordinate))

theorem reciprocalRaw_gap (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (small : |x| < 4) : reciprocalRaw coordinate x = 0 :=
  if_neg (not_le_of_gt small)

theorem coSum_gap (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ} (small : |x| < 4) :
    burnolInnerGapForward (reciprocalRaw coordinate) x = 0 := by
  unfold burnolInnerGapForward
  have term (n : ℕ+) : (((n : ℕ) : ℂ)⁻¹) * reciprocalRaw coordinate (x / (n : ℕ)) = 0 := by
    have positive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
    have one : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
    have divided : |x / (n : ℕ)| < 4 := by
      rw [abs_div, abs_of_pos positive]
      exact (div_le_self (abs_nonneg x) one).trans_lt small
    rw [reciprocalRaw_gap coordinate divided, mul_zero]
  simpa only [tsum_zero] using tsum_congr term

/-- The previously computed original mean cancels the same full-source normalization. -/
theorem original_fourier_coSum (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (AmbientCounting.value coordinate) : ℝ → ℂ) =ᵐ[volume]
      burnolInnerGapForward (reciprocalRaw coordinate) := by
  let original := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let dual := burnolTateReciprocalL2 original
  let value := fourierL2 (AmbientCounting.value coordinate)
  have dualEven : reflectL2 dual = dual := burnolReflectL2_eq_of_even_raw dual _
    (reciprocalRaw_read coordinate) (fun x => by simp only [reciprocalRaw, abs_neg])
  have dualGap : (dual : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae (reciprocalRaw_read coordinate),
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
    rw [read, reciprocalRaw_gap coordinate (by linarith [abs_le.mpr inside])]
  have realization (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead dual test =
      ∫ x : ℝ, test x * value x := by
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      burnolRemainderRealization_fourier original (AmbientCounting.value coordinate)
        (AmbientFourier.original_realizes coordinate) test
  obtain ⟨representative, represents, _, valueRep⟩ :=
    burnolRemainderSourceRead_realization_ae dual value dualEven dualGap realization
  let mean := ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * representative u
  have same := represents.symm.trans (reciprocalRaw_read coordinate)
  have sumRead := burnolInnerGapForward_ae_congr representative (reciprocalRaw coordinate) same
  have fullRead : (value : ℝ → ℂ) =ᵐ[volume]
      fun x => burnolInnerGapForward (reciprocalRaw coordinate) x - mean := by
    filter_upwards [valueRep, sumRead] with x read sumAt
    rw [read, sumAt]
  have constantRead : burnolQuarterRestriction value = -mean • intervalConstant q := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
      ae_restrict_of_ae fullRead, ae_restrict_mem (measurableSet_symmetricInterval q),
      Lp.coeFn_smul (-mean) (intervalConstant q), intervalConstant_coeFn q]
        with x restricted read inside smulAt constantAt
    change burnolQuarterRestriction value x = _ at restricted
    rw [restricted, read, coSum_gap coordinate (by linarith [abs_le.mpr inside]), zero_sub, smulAt]
    change -mean = -mean * intervalConstant q x
    rw [constantAt, mul_one]
  rw [AmbientFourier.original_fourier_gap coordinate] at constantRead
  have meanZero : mean = 0 := neg_eq_zero.mp
    ((smul_eq_zero.mp constantRead.symm).resolve_right (intervalConstant_ne_zero (by norm_num)))
  simpa only [meanZero, sub_zero] using fullRead

theorem reciprocal_channel (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (nonzero : x ≠ 0) (n : ℕ+) :
    (((n : ℕ) : ℂ)⁻¹) * reciprocalRaw coordinate (x / (n : ℕ)) =
      if (n : ℕ) ∈ channels x then ((|x| : ℝ) : ℂ)⁻¹ *
        burnolRieszSingleFourierSourceRaw coordinate ((n : ℕ) / |x|) else 0 := by
  have positive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have incidence : 4 ≤ |x / (n : ℕ)| ↔ (n : ℕ) ∈ channels x := by
    simp only [channels, Finset.mem_Icc, show 1 ≤ (n : ℕ) from n.pos, true_and, abs_div, abs_of_pos positive,
      Nat.le_floor_iff' n.pos.ne', le_div_iff₀ positive, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    exact mul_comm (4 : ℝ) (n : ℕ) ▸ Iff.rfl
  unfold reciprocalRaw
  simp only [incidence]
  split_ifs
  · rw [ReciprocalTail.weight, abs_div, abs_of_pos positive, inv_div, Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr absolute.ne', show ((n : ℕ) : ℂ) ≠ 0 by exact_mod_cast n.pos.ne']
    push_cast
    ring
  · exact mul_zero _

theorem coSum_eq_raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolInnerGapForward (reciprocalRaw coordinate) x = raw coordinate x := by
  classical
  by_cases zero : x = 0
  · simp only [zero, coSum_gap coordinate (by norm_num : |(0 : ℝ)| < 4), raw, abs_zero,
      Complex.ofReal_zero, inv_zero, zero_mul]
  let term : ℕ → ℂ := fun n => if n ∈ channels x then
    ((|x| : ℝ) : ℂ)⁻¹ * burnolRieszSingleFourierSourceRaw coordinate ((n : ℝ) / |x|) else 0
  have support : Function.support term ⊆ {n : ℕ | 0 < n} := by
    intro n active
    have belongs : n ∈ channels x := by
      by_contra outside
      exact active (if_neg outside)
    exact (Finset.mem_Icc.mp belongs).1
  calc
    _ = ∑' n : ℕ+, term (n : ℕ) := by
      apply tsum_congr
      exact reciprocal_channel coordinate x zero
    _ = ∑' n : ℕ, term n := tsum_subtype_eq_of_support_subset support
    _ = ∑ n ∈ channels x, term n := tsum_eq_sum (fun n outside => if_neg outside)
    _ = _ := by
      simp only [term, Finset.sum_ite_mem, Finset.inter_self, raw, Finset.mul_sum]

theorem original_fourier_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (AmbientCounting.value coordinate) : ℝ → ℂ) =ᵐ[volume] raw coordinate :=
  (original_fourier_coSum coordinate).trans (Eventually.of_forall (coSum_eq_raw coordinate))

theorem raw_gap (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ} (small : |x| < 4) :
    raw coordinate x = 0 := (coSum_eq_raw coordinate x).symm.trans (coSum_gap coordinate small)

/-- The endpoint is kept in the raw formula; it is null for the closed L² window. -/
theorem original_fourier_gap_four (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusRestriction 4 (fourierL2 (AmbientCounting.value coordinate)) = 0 := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval 4) (fourierL2 (AmbientCounting.value coordinate)),
    ae_restrict_of_ae (original_fourier_coeFn coordinate), ae_restrict_mem (measurableSet_symmetricInterval 4),
    ae_restrict_of_ae (volume.ae_ne (4 : ℝ)), ae_restrict_of_ae (volume.ae_ne (-4 : ℝ)),
    Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval (4 : ℝ)))]
      with x restricted read inside upper lower zeroAt
  change burnolRadiusRestriction 4 (fourierL2 (AmbientCounting.value coordinate)) x = _ at restricted
  have small : |x| < 4 := abs_lt.mpr ⟨lt_of_le_of_ne inside.1 lower.symm, lt_of_le_of_ne inside.2 upper⟩
  rw [restricted, read, raw_gap coordinate small, zeroAt]
  rfl

theorem raw_first_band (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (lower : 4 ≤ |x|) (upper : |x| < 8) :
    raw coordinate x = ReciprocalTail.weight coordinate |x| := by
  have index : ⌊|x| / 4⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ |x| / 4)]
    constructor <;> norm_num <;> linarith
  unfold raw channels
  rw [index]
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one,
    ReciprocalTail.weight, div_eq_mul_inv]
  ring

theorem original_first_band (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (AmbientCounting.value coordinate) : ℝ → ℂ) =ᵐ[volume.restrict (Icc 4 8)]
      ReciprocalTail.weight coordinate := by
  filter_upwards [ae_restrict_of_ae (original_fourier_coeFn coordinate),
    ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (8 : ℝ))]
      with x read inside notEndpoint
  have positive : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 4).trans inside.1
  rw [read, raw_first_band coordinate x (by rw [abs_of_nonneg positive]; exact inside.1)
    (by rw [abs_of_nonneg positive]; exact lt_of_le_of_ne inside.2 notEndpoint), abs_of_nonneg positive]

theorem raw_second_endpoint (coordinate : BurnolCompletedMellinCoordinate) :
    raw coordinate 8 = (8 : ℂ)⁻¹ *
      (burnolRieszSingleFourierSourceRaw coordinate (1 / 8) +
        burnolRieszSingleFourierSourceRaw coordinate q) := by
  norm_num [raw, channels, Finset.sum_Icc_succ_top]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.AmbientFourierRaw
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
