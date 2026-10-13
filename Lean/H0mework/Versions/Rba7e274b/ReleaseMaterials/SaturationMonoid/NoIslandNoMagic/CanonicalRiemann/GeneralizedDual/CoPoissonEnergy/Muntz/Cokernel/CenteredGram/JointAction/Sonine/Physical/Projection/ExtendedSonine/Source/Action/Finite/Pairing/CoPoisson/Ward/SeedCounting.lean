import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SeedCounting

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalPaPhysicalGreen OriginalRieszFiniteColumns
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem source_sub (N : ℕ) (left right : BurnolL2) :
    FiniteForcing.source N (left - right) = FiniteForcing.source N left - FiniteForcing.source N right := by
  unfold FiniteForcing.source ContinuousChannels.normalization
  simp only [Channels.sourceChannel, ContinuousChannels.channel, map_sub, smul_sub, Finset.sum_sub_distrib]
  have difference := integral_sub (ContinuousChannels.channel_integrable (-1) N left)
    (ContinuousChannels.channel_integrable (-1) N right)
  simp only [ContinuousChannels.channel] at difference
  rw [difference]
  abel

theorem source_dilation (N : ℕ) (time : ℝ) (seed : BurnolL2) :
    FiniteForcing.source N (burnolMultiplicativeDilation time seed) =
      burnolMultiplicativeDilation time (FiniteForcing.source N seed) := by
  have channel (radius : ℝ) :
      ContinuousChannels.channel (-1) radius (burnolMultiplicativeDilation time seed) =
        burnolMultiplicativeDilation time (ContinuousChannels.channel (-1) radius seed) := by
    simp only [ContinuousChannels.channel, map_smul, burnolMultiplicativeDilation_add]
    rw [add_comm]
  have integer (n : ℕ) : Channels.sourceChannel n (burnolMultiplicativeDilation time seed) =
      burnolMultiplicativeDilation time (Channels.sourceChannel n seed) := by
    simp only [Channels.sourceChannel, map_smul, burnolMultiplicativeDilation_add]
    rw [add_comm]
  unfold FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact (burnolMultiplicativeDilation time).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) N seed)

private theorem fourier_seed_window (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    let extension := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    fourierSeed coordinate shift = originalPhysicalCutoff q
      (burnolMultiplicativeDilation (-shift) extension) - burnolMultiplicativeDilation (-shift) extension := by
  dsimp only
  rw [fourierSeed_eq_exterior coordinate shift nonnegative, fourierColumn_action]
  let extension := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  have cutoff : originalPhysicalCutoff q extension = extension := by
    change burnolQuarterZeroExtension (burnolQuarterRestriction (burnolQuarterZeroExtension _)) = _
    rw [burnolQuarterRestriction_zeroExtension]
  change _ = originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) extension) -
    burnolMultiplicativeDilation (-shift) extension
  have split (left right : BurnolL2) : originalPhysicalCutoff q (left - right) =
      originalPhysicalCutoff q left - originalPhysicalCutoff q right := by
    simp only [originalPhysicalCutoff, map_sub]
  have scaled (scalar : ℂ) : originalPhysicalCutoff q (scalar • extension) = scalar • extension := by
    simpa only [originalPhysicalCutoff, map_smul] using congrArg (scalar • ·) cutoff
  rw [split, scaled]
  module

/-- The actual weighted seed retains the cutoff in its original order under finite counting. -/
theorem fourier_seed_source (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) :
    let extension := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    FiniteForcing.source N (fourierSeed coordinate shift) =
      FiniteForcing.source N (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) extension)) -
      burnolMultiplicativeDilation (-shift) (FiniteForcing.source N extension) := by
  dsimp only
  rw [fourier_seed_window coordinate shift nonnegative, source_sub, source_dilation]

theorem fourier_seed_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) (test : BurnolL2) :
    let extension := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    inner ℂ (FiniteForcing.source N (fourierSeed coordinate shift)) test =
      inner ℂ (FiniteForcing.source N
        (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) extension))) test -
      inner ℂ (FiniteForcing.source N extension) (burnolMultiplicativeDilation shift test) := by
  dsimp only
  rw [fourier_seed_source coordinate shift nonnegative, inner_sub_left]
  have moved := (burnolMultiplicativeDilation (-shift)).inner_map_eq_flip
    (FiniteForcing.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) test
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at moved
  rw [moved]

/-- The original Pa zero law consumes the complete transported pair; neither moved read is removed. -/
theorem original_fourier_seed_limit (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    let extension := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    let test := fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    Tendsto (fun N : ℕ =>
      inner ℂ (FiniteForcing.source N
        (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) extension))) test -
      inner ℂ (FiniteForcing.source N extension) (burnolMultiplicativeDilation shift test)) atTop (𝓝 0) := by
  dsimp only
  have regular : Continuous (fun value : BurnolL2 =>
      inner ℂ value (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) := by fun_prop
  have actual := (regular.tendsto (fourierWave coordinate shift)).comp
    (fourierPrefix_tendsto coordinate shift)
  rw [fourierWave_zero_read coordinate zero shift nonnegative bounded] at actual
  convert! actual using 1
  funext N
  simp only [Function.comp_apply]
  rw [← fourier_seed_pairing coordinate shift nonnegative,
    FiniteForcing.fourier_read, FiniteForcing.fourierPrefix_read coordinate shift nonnegative]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SeedCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
