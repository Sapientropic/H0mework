import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FirstBandNormalization
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SteinExpansion
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDualSupport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.FirstBandCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalPaPhysicalGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "K" => burnolCompletedMellinRieszVector

private theorem original_gap (coordinate : BurnolCompletedMellinCoordinate) :
    ((K coordinate : BurnolL2) : ℝ → ℂ) =ᵐ[μq] fun _ => positionMean coordinate := by
  filter_upwards [ae_restrict_of_ae (burnolRieszState_ae_raw coordinate),
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
  rw [read, position_raw, if_pos inside, add_zero]

private theorem gap_pair (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : value = E (burnolQuarterRestriction value)) :
    inner ℂ (K coordinate : BurnolL2) value =
      star (positionMean coordinate) * ∫ x : ℝ, value x := by
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (original_gap coordinate)
  have cutoff : originalPhysicalCutoff q value = value := supported.symm
  have cut := originalPhysicalCutoff_coeFn q value
  rw [cutoff] at cut
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [gap, cut] with x read support
  by_cases inside : x ∈ symmetricInterval q
  · rw [read inside, RCLike.inner_apply]
    simp only [starRingEnd_apply]
    ring
  · rw [support, indicator_of_notMem inside]
    simp

private theorem defect_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectRestricted q (SteinEnergy.defect coordinate : Hq) = SteinEnergy.defect coordinate := by
  have opposite := (negMeasurePreserving_restrict q).quasiMeasurePreserving.ae
    (SteinRaw.defect_coeFn coordinate)
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (SteinEnergy.defect coordinate : Hq)
    (negMeasurePreserving_restrict q), SteinRaw.defect_coeFn coordinate, opposite]
    with x reflection actual negative
  change reflectRestricted q (SteinEnergy.defect coordinate : Hq) x =
    (SteinEnergy.defect coordinate : Hq) (-x) at reflection
  rw [reflection, negative, actual]
  simp only [symmetricInterval, mem_Icc, ← abs_le, abs_neg, return_raw_even]

private theorem shifted_gap (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (nonpositive : h ≤ 0) :
    burnolQuarterRestriction (burnolMultiplicativeDilation h (K coordinate : BurnolL2)) =
      ((Real.exp (h / 2) : ℂ) * positionMean coordinate) • intervalConstant q := by
  have sourceRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (original_gap coordinate)
  have scaled : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolMultiplicativeDilation h (K coordinate : BurnolL2)),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn h (K coordinate : BurnolL2)),
    ae_restrict_of_ae (scaled.ae sourceRead), ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul ((Real.exp (h / 2) : ℂ) * positionMean coordinate) (intervalConstant q),
    intervalConstant_coeFn q] with x restricted dilated source inside smulAt constant
  have stays : Real.exp h * x ∈ symmetricInterval q := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos (Real.exp_pos h)]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr nonpositive) (abs_nonneg x)).trans
      (by simpa only [one_mul] using abs_le.mpr inside)
  change burnolQuarterRestriction (burnolMultiplicativeDilation h (K coordinate : BurnolL2)) x = _ at restricted
  rw [restricted, dilated, smulAt]
  change (Real.exp (h / 2) : ℂ) * (K coordinate : BurnolL2) (Real.exp h * x) =
    ((Real.exp (h / 2) : ℂ) * positionMean coordinate) * intervalConstant q x
  rw [source stays, constant, mul_one]

private theorem contracted_pair_zero (coordinate : BurnolCompletedMellinCoordinate)
    (state : M) (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (K coordinate : BurnolL2) (burnolMultiplicativeDilation h (E (state : Hq))) = 0 := by
  have flipped := (burnolMultiplicativeDilation (-h)).inner_map_eq_flip
    (K coordinate : BurnolL2) (E (state : Hq))
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at flipped
  have restricted := ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction
    (burnolMultiplicativeDilation (-h) (K coordinate : BurnolL2)) (state : Hq)
  change inner ℂ (burnolMultiplicativeDilation (-h) (K coordinate : BurnolL2)) (E (state : Hq)) = _ at restricted
  rw [← flipped, restricted, shifted_gap coordinate (-h) (neg_nonpos.mpr nonnegative), inner_smul_left]
  have mean : inner ℂ (intervalConstant q) (state : Hq) = 0 :=
    (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  rw [mean, mul_zero]

/-- Every integer beyond the first contracts the full mean-zero source into the actual K gap. -/
theorem integer_pair (coordinate : BurnolCompletedMellinCoordinate) (state : M)
    (n : ℕ) (large : 2 ≤ n) :
    inner ℂ (K coordinate : BurnolL2)
      (ContinuousChannels.channel 1 (n : ℝ)
        (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq)))) = 0 := by
  rw [ContinuousChannels.channel, one_mul, burnolMultiplicativeDilation_add, inner_smul_right]
  have nonnegative : 0 ≤ Real.log (n : ℝ) + -Real.log 2 := by
    have monotone := Real.strictMonoOn_log.monotoneOn
      (show (2 : ℝ) ∈ Ioi 0 by norm_num)
      (show (n : ℝ) ∈ Ioi 0 by
        have lower : (2 : ℝ) ≤ n := by exact_mod_cast large
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) lower)
      (show (2 : ℝ) ≤ n by exact_mod_cast large)
    linarith
  rw [contracted_pair_zero coordinate state _ nonnegative, mul_zero]

/-- The same N retains the genuine first integer and its complete continuous compensation. -/
theorem finite_integer_read (coordinate : BurnolCompletedMellinCoordinate) (state : M)
    (N : ℕ) (large : 2 ≤ N) :
    inner ℂ (K coordinate : BurnolL2)
      (DualSource.source N (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq)))) =
      inner ℂ (K coordinate : BurnolL2) (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq))) -
        inner ℂ (K coordinate : BurnolL2)
          (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a
            (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq)))) := by
  rw [DualSource.source, inner_sub_right, inner_sum]
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp only [Nat.cast_one, ContinuousChannels.channel, Real.sqrt_one, Complex.ofReal_one,
      inv_one, Real.log_one, mul_zero, burnolMultiplicativeDilation_zero, one_smul]
  · intro n member different
    exact integer_pair coordinate state n (by have := (Finset.mem_Ico.mp member).1; omega)
  · intro absent
    exact (absent (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)).elim


/-- The complete programme stabilizes on this actual mean-zero expanded source from N=2 onward. -/
theorem original_finite (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (large : 2 ≤ N) :
    inner ℂ (FiniteForcing.source N (K coordinate : BurnolL2)) (SteinExpansion.expanded coordinate) =
      inner ℂ (K coordinate : BurnolL2) (SteinExpansion.expanded coordinate) +
        (Real.sqrt 2 : ℂ) * star (positionMean coordinate) *
          inner ℂ SmallScaleLog.logL2 (SteinEnergy.defect coordinate : Hq) := by
  have support := FirstBandNormalization.shifted_support (SteinEnergy.defect coordinate)
    (defect_even coordinate) (N : ℝ) (by exact_mod_cast large)
  have mass := FirstBandNormalization.shifted_integral (SteinEnergy.defect coordinate)
    (defect_even coordinate) (N : ℝ) (by exact_mod_cast large)
  rw [CountingDual.source_pairing, SteinExpansion.expanded, finite_integer_read coordinate _ N large]
  change _ - inner ℂ (K coordinate : BurnolL2)
    (FirstBandNormalization.normalPlus (N : ℝ)
      (burnolMultiplicativeDilation (-Real.log 2) (E (SteinEnergy.defect coordinate : Hq)))) = _
  rw [gap_pair coordinate _ support, mass]
  ring

/-- This scalar limit needs no zeta-zero assumption: its entire finite source is already constant in N. -/
theorem original_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => inner ℂ (FiniteForcing.source N (K coordinate : BurnolL2))
      (SteinExpansion.expanded coordinate)) atTop
      (𝓝 (inner ℂ (K coordinate : BurnolL2) (SteinExpansion.expanded coordinate) +
        (Real.sqrt 2 : ℂ) * star (positionMean coordinate) *
          inner ℂ SmallScaleLog.logL2 (SteinEnergy.defect coordinate : Hq))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N large
  exact (original_finite coordinate N large).symm

/-- The original zero-owned K strong limit consumes that same complete source value. -/
theorem original_pair (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (KCountingGram.value coordinate) (SteinExpansion.expanded coordinate) =
      inner ℂ (K coordinate : BurnolL2) (SteinExpansion.expanded coordinate) +
        (Real.sqrt 2 : ℂ) * star (positionMean coordinate) *
          inner ℂ SmallScaleLog.logL2 (SteinEnergy.defect coordinate : Hq) := by
  exact tendsto_nhds_unique ((KCountingGram.forward_tendsto coordinate zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := SteinExpansion.expanded coordinate))) (original_tendsto coordinate)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.FirstBandCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
