import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.ScaleRatio

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DualShell

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalPaPhysicalGreen OriginalRieszFiniteColumns
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem event_collar (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (lower : q / 2 < |x|) (upper : |x| ≤ q) :
    DualSourceRaw.eventRaw coordinate x = DualSourceRaw.seedRaw coordinate x := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q / 2).trans lower
  have index : ⌊q / |x|⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ q / |x|)]
    constructor
    · norm_num
      exact (le_div_iff₀ absolute).mpr (by simpa using upper)
    · norm_num
      exact (div_lt_iff₀ absolute).mpr (by linarith)
  have member : (1 : ℕ) ∈ DualSourceRaw.channels x := by
    rw [DualSourceRaw.channels, index]
    simp
  have first := DualSourceRaw.seedRaw_channel coordinate x (abs_pos.mp absolute) 1 (by norm_num)
  simp only [Nat.cast_one, one_mul, if_pos member] at first
  rw [DualSourceRaw.eventRaw, DualSourceRaw.channels, index, Finset.Icc_self, Finset.sum_singleton]
  simpa only [Nat.cast_one, one_mul] using first.symm

/-- Once N includes channel one, the original outer half-collar is read exactly from b. -/
theorem raw_outside_half (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (after : 2 ≤ N)
    (x : ℝ) (outside : q / 2 < |x|) :
    DualSourceRaw.raw coordinate N x = DualSourceRaw.seedRaw coordinate x := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q / 2).trans outside
  by_cases inside : |x| ≤ q
  · have complete : q / |x| < (N : ℝ) := by
      have large : (2 : ℝ) ≤ N := by exact_mod_cast after
      exact ((div_lt_iff₀ absolute).mpr (by linarith : q < 2 * |x|)).trans_le large
    rw [DualSourceRaw.raw_event coordinate N x (abs_pos.mp absolute) complete]
    exact event_collar coordinate x outside inside
  · rw [DualSourceRaw.raw_outside coordinate N (by omega) x (lt_of_not_ge inside)]
    unfold DualSourceRaw.seedRaw
    have notInside : x ∉ symmetricInterval q := fun member => inside (abs_le.mpr member)
    rw [indicator_of_notMem notInside]

/-- The new finite dual contribution is genuinely supported in the original closed half-window. -/
theorem finite_difference_support (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (after : 2 ≤ N) :
    let seed := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    originalPhysicalCutoff (q / 2) (DualSource.source N seed - seed) = DualSource.source N seed - seed := by
  dsimp only
  apply cutoff_eq_self_of_ae_zero
  filter_upwards [Lp.coeFn_sub (DualSource.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)),
    DualSourceRaw.original_coeFn coordinate N, DualSourceRaw.seedRaw_read coordinate]
      with x difference original seed outside
  rw [difference]
  change _ - _ = (0 : ℂ)
  rw [original, seed, raw_outside_half coordinate N after x
    (lt_of_not_ge (fun inside => outside (abs_le.mp inside))), sub_self]

/-- The independently generated strong limit retains this same closed support. -/
theorem limit_difference_support (coordinate : BurnolCompletedMellinCoordinate) :
    let seed := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    originalPhysicalCutoff (q / 2) (CountingDual.value coordinate - seed) = CountingDual.value coordinate - seed := by
  dsimp only
  let seed := burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  have sourceLimit := (CountingDual.original_dual_tendsto coordinate).sub_const seed
  have continuousCut : Continuous (originalPhysicalCutoff (q / 2)) := by
    unfold originalPhysicalCutoff
    fun_prop
  have cutLimit := (continuousCut.tendsto (CountingDual.value coordinate - seed)).comp sourceLimit
  have same := cutLimit.congr' (show _ =ᶠ[atTop]
      (fun N : ℕ => DualSource.source N seed - seed) from by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N after
    exact finite_difference_support coordinate N after)
  exact tendsto_nhds_unique same sourceLimit

private theorem cutoff_mono (small large : ℝ) (ordered : small ≤ large) (value : BurnolL2)
    (supported : originalPhysicalCutoff small value = value) : originalPhysicalCutoff large value = value := by
  apply cutoff_eq_self_of_ae_zero
  filter_upwards [originalPhysicalCutoff_coeFn small value] with x read outside
  rw [supported] at read
  rw [read, indicator_of_notMem (fun inside => outside ⟨by linarith [inside.1], inside.2.trans ordered⟩)]

private theorem half_difference_shell (value seed : BurnolL2) (shift : ℝ) (bounded : shift ≤ Real.log 2)
    (supported : originalPhysicalCutoff (q / 2) (value - seed) = value - seed) :
    originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value) -
        burnolMultiplicativeDilation (-shift) value =
      originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed) -
        burnolMultiplicativeDilation (-shift) seed := by
  have half : (1 / 2 : ℝ) ≤ Real.exp (-shift) := by
    have original := Real.exp_le_exp.mpr (neg_le_neg bounded)
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using original
  have included : q / 2 ≤ Real.exp (-shift) * q := by nlinarith
  have cut := cutoff_mono (q / 2) (Real.exp (-shift) * q) included (value - seed) supported
  have moved : originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) (value - seed)) =
      burnolMultiplicativeDilation (-shift) (value - seed) := by
    rw [originalPhysicalCutoff_dilation, cut]
  simp only [map_sub] at moved
  change burnolRadiusZeroExtension q (burnolRadiusRestriction q
      (burnolMultiplicativeDilation (-shift) value - burnolMultiplicativeDilation (-shift) seed)) = _ at moved
  rw [map_sub, map_sub] at moved
  apply sub_eq_zero.mp
  calc
    _ = (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value) -
        originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed)) -
        (burnolMultiplicativeDilation (-shift) value - burnolMultiplicativeDilation (-shift) seed) := by abel
    _ = 0 := sub_eq_zero.mpr moved

private theorem original_seed_window (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) :
    let seed := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    fourierSeed coordinate shift = originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed) -
      burnolMultiplicativeDilation (-shift) seed := by
  dsimp only
  rw [fourierSeed_eq_exterior coordinate shift nonnegative, fourierColumn_action]
  let seed := burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  have cut : originalPhysicalCutoff q seed = seed := by
    change burnolQuarterZeroExtension (burnolQuarterRestriction (burnolQuarterZeroExtension _)) = _
    rw [burnolQuarterRestriction_zeroExtension]
  change _ = originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed) -
    burnolMultiplicativeDilation (-shift) seed
  have split (left right : BurnolL2) : originalPhysicalCutoff q (left - right) =
      originalPhysicalCutoff q left - originalPhysicalCutoff q right := by
    simp only [originalPhysicalCutoff, map_sub]
  have scalar (a : ℂ) : originalPhysicalCutoff q (a • seed) = a • seed := by
    simpa only [originalPhysicalCutoff, map_smul] using congrArg (a • ·) cut
  rw [split, scalar]
  module

/-- The original Fourier seed is the actual shell of every finite dual after channel one. -/
theorem finite_fourier_seed (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (after : 2 ≤ N)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    let seed := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    fourierSeed coordinate shift =
      originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) (DualSource.source N seed)) -
        burnolMultiplicativeDilation (-shift) (DualSource.source N seed) := by
  dsimp only
  exact (original_seed_window coordinate shift nonnegative).trans
    (half_difference_shell _ _ shift bounded (finite_difference_support coordinate N after)).symm

/-- The same original shell is retained by the genuinely generated ambient dual limit. -/
theorem limit_fourier_seed (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    fourierSeed coordinate shift =
      originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) (CountingDual.value coordinate)) -
        burnolMultiplicativeDilation (-shift) (CountingDual.value coordinate) := by
  exact (original_seed_window coordinate shift nonnegative).trans
    (half_difference_shell _ _ shift bounded (limit_difference_support coordinate)).symm

private theorem shell_pairing (value : BurnolL2) (shift : ℝ) (N : ℕ) (test : BurnolL2) :
    inner ℂ (FiniteForcing.source N (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value) -
      burnolMultiplicativeDilation (-shift) value)) test =
    inner ℂ (FiniteForcing.source N (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value))) test -
      inner ℂ (FiniteForcing.source N value) (burnolMultiplicativeDilation shift test) := by
  have linear := map_sub (CountingDual.sourceCLM N)
    (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value)) (burnolMultiplicativeDilation (-shift) value)
  simp only [CountingDual.sourceCLM_apply] at linear
  rw [linear, inner_sub_left, SeedCounting.source_dilation]
  have moved := (burnolMultiplicativeDilation (-shift)).inner_map_eq_flip (FiniteForcing.source N value) test
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at moved
  rw [moved]

private theorem after_source_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2)
    (value : BurnolL2) (shell : fourierSeed coordinate shift =
      originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value) - burnolMultiplicativeDilation (-shift) value) :
    Tendsto (fun N : ℕ =>
      inner ℂ (FiniteForcing.source N (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value)))
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
      inner ℂ (FiniteForcing.source N value)
        (burnolMultiplicativeDilation shift (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))))
      atTop (𝓝 0) := by
  have original := SeedCounting.original_fourier_seed_limit coordinate zero shift nonnegative bounded
  apply original.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [← SeedCounting.fourier_seed_pairing coordinate shift nonnegative N,
    shell, shell_pairing]

/-- The original Pa law consumes the complete after-dual finite pair through its identical source shell. -/
theorem finite_after_dual_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (N : ℕ) (after : 2 ≤ N)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    let value := DualSource.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))
    Tendsto (fun M : ℕ =>
      inner ℂ (FiniteForcing.source M (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) value)))
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
      inner ℂ (FiniteForcing.source M value)
        (burnolMultiplicativeDilation shift (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))))
      atTop (𝓝 0) :=
  after_source_zero coordinate zero shift nonnegative bounded _ (finite_fourier_seed coordinate N after shift nonnegative bounded)

/-- The same original Pa consumer reads the full source pair after the independent ambient dual limit. -/
theorem limit_after_dual_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    Tendsto (fun N : ℕ =>
      inner ℂ (FiniteForcing.source N
        (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) (CountingDual.value coordinate))))
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
      inner ℂ (FiniteForcing.source N (CountingDual.value coordinate))
        (burnolMultiplicativeDilation shift (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))))
      atTop (𝓝 0) :=
  after_source_zero coordinate zero shift nonnegative bounded _ (limit_fourier_seed coordinate shift nonnegative bounded)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DualShell
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
