import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Channels
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousNormalization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.FiniteForcing

open Complex MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFiniteSource
noncomputable section

def source (N : ℕ) (seed : BurnolL2) : BurnolL2 :=
  (∑ n ∈ Finset.Ico 1 N, Channels.sourceChannel n seed) -
    ContinuousChannels.normalization N seed

def coefficient (value : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-value)) -
    (N : ℂ) ^ (1 - value) / (1 - value)

def positionForcing (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  (∑ n ∈ Finset.Ico 1 N, (Real.sqrt (n : ℝ) : ℂ)⁻¹ •
    forcingIntegral coordinate (Real.log (n : ℝ))) -
  ∫ radius : ℝ in Ioc 0 (N : ℝ), (Real.sqrt radius : ℂ)⁻¹ •
    forcingIntegral coordinate (Real.log radius)

def fourierForcing (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  (∑ n ∈ Finset.Ico 1 N, (Real.sqrt (n : ℝ) : ℂ)⁻¹ •
    fourierL2 (forcingIntegral coordinate (-Real.log (n : ℝ)))) -
  ∫ radius : ℝ in Ioc 0 (N : ℝ), (Real.sqrt radius : ℂ)⁻¹ •
    fourierL2 (forcingIntegral coordinate (-Real.log radius))

private theorem position_channel (coordinate : BurnolCompletedMellinCoordinate)
    (seed : BurnolL2) (n : ℕ) (positive : 0 < n) :
    inner ℂ (Channels.sourceChannel n seed) (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      (n : ℂ) ^ (-star coordinate.value) *
        inner ℂ seed (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      inner ℂ seed ((Real.sqrt (n : ℝ) : ℂ)⁻¹ •
        forcingIntegral coordinate (Real.log (n : ℝ))) := by
  rw [Channels.sourceChannel_pairing]
  have actual := congrArg (fun value : BurnolL2 => inner ℂ seed value)
    (ContinuousChannels.kernel_action coordinate n (by exact_mod_cast positive))
  simpa only [ContinuousChannels.channel, one_mul, inner_smul_right, inner_add_right,
    Complex.ofReal_natCast] using actual

private theorem fourier_channel (coordinate : BurnolCompletedMellinCoordinate)
    (seed : BurnolL2) (n : ℕ) (positive : 0 < n) :
    inner ℂ (Channels.sourceChannel n seed)
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      (n : ℂ) ^ (-(1 - star coordinate.value)) *
        inner ℂ seed (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) +
      inner ℂ seed ((Real.sqrt (n : ℝ) : ℂ)⁻¹ •
        fourierL2 (forcingIntegral coordinate (-Real.log (n : ℝ)))) := by
  rw [Channels.sourceChannel_pairing]
  have actual := congrArg (fun value : BurnolL2 => inner ℂ seed value)
    (ContinuousChannels.fourier_kernel_action coordinate n (by exact_mod_cast positive))
  simpa only [ContinuousChannels.channel, one_mul, inner_smul_right, inner_add_right,
    Complex.ofReal_natCast, neg_sub] using actual

/-- The finite integer action and its same-cutoff continuous compensation
retain exactly their centered arithmetic coefficient and original source forcing. -/
theorem position_read (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (seed : BurnolL2) :
    inner ℂ (source N seed) (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      coefficient (star coordinate.value) N *
        inner ℂ seed (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      inner ℂ seed (positionForcing coordinate N) := by
  classical
  unfold source positionForcing coefficient
  rw [inner_sub_left, sum_inner, ContinuousChannels.normalization_kernel coordinate N (by positivity)]
  have channels : (∑ n ∈ Finset.Ico 1 N,
      inner ℂ (Channels.sourceChannel n seed) (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      ∑ n ∈ Finset.Ico 1 N, ((n : ℂ) ^ (-star coordinate.value) *
        inner ℂ seed (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      inner ℂ seed ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • forcingIntegral coordinate (Real.log (n : ℝ)))) := by
    apply Finset.sum_congr rfl
    intro n member
    exact position_channel coordinate seed n
      (Nat.lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Ico.mp member).1)
  rw [channels, Finset.sum_add_distrib, ← Finset.sum_mul, inner_sub_right, inner_sum]
  push_cast
  ring

theorem fourier_read (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (seed : BurnolL2) :
    inner ℂ (source N seed) (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      coefficient (1 - star coordinate.value) N *
        inner ℂ seed (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) +
      inner ℂ seed (fourierForcing coordinate N) := by
  classical
  unfold source fourierForcing coefficient
  rw [inner_sub_left, sum_inner,
    ContinuousChannels.normalization_fourier_kernel coordinate N (by positivity)]
  have channels : (∑ n ∈ Finset.Ico 1 N,
      inner ℂ (Channels.sourceChannel n seed)
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) =
      ∑ n ∈ Finset.Ico 1 N, ((n : ℂ) ^ (-(1 - star coordinate.value)) *
        inner ℂ seed (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) +
      inner ℂ seed ((Real.sqrt (n : ℝ) : ℂ)⁻¹ •
        fourierL2 (forcingIntegral coordinate (-Real.log (n : ℝ))))) := by
    apply Finset.sum_congr rfl
    intro n member
    exact fourier_channel coordinate seed n
      (Nat.lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Ico.mp member).1)
  rw [channels, Finset.sum_add_distrib, ← Finset.sum_mul, inner_sub_right, inner_sum]
  simp only [sub_sub_cancel]
  push_cast
  ring

private theorem reciprocalWeight_measurable (shift : ℝ) (profile : ℝ → ℂ)
    (measured : Measurable profile) : Measurable (reciprocalWeight shift profile) := by
  unfold reciprocalWeight
  exact (measurable_const.mul Complex.measurable_ofReal.inv).mul
    (measured.comp (measurable_const.div measurable_id))

private theorem positionWeight_measurable (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    Measurable (positionWeight coordinate shift) := by
  apply reciprocalWeight_measurable
  have power : Measurable (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (Complex.continuousAt_ofReal_cpow_const x (-star coordinate.value)
      (Or.inr (by simpa only [mem_compl_iff, mem_singleton_iff] using outside))).continuousWithinAt
  exact ((measurable_const.mul power).sub_const _).sub
    (burnolRieszReturnRaw_continuous coordinate).measurable

private theorem fourierWeight_measurable (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    Measurable (fourierWeight coordinate shift) := by
  apply reciprocalWeight_measurable
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  exact (burnolRieszSingleFourierSourceRaw_continuousAt coordinate
    (by simpa only [mem_compl_iff, mem_singleton_iff] using outside)).continuousWithinAt

private theorem positionPrefix_source (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) :
    positionPrefix coordinate shift N = source N (positionSeed coordinate shift) :=
  weighted_prefix_eq_finite_sub_continuous _ _ _ _ N (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => positionWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _)
    (positionWeight_measurable coordinate shift)

private theorem fourierPrefix_source (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) :
    fourierPrefix coordinate shift N = source N (fourierSeed coordinate shift) :=
  weighted_prefix_eq_finite_sub_continuous _ _ _ _ N (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => fourierWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _)
    (fourierWeight_measurable coordinate shift)

theorem positionPrefix_read (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) :
    inner ℂ (positionPrefix coordinate shift N)
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      coefficient (star coordinate.value) N *
        inner ℂ (positionSeed coordinate shift) (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      inner ℂ (positionSeed coordinate shift) (positionForcing coordinate N) := by
  rw [positionPrefix_source coordinate shift nonnegative, position_read]

theorem fourierPrefix_read (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) :
    inner ℂ (fourierPrefix coordinate shift N)
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      coefficient (1 - star coordinate.value) N *
        inner ℂ (fourierSeed coordinate shift)
          (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) +
      inner ℂ (fourierSeed coordinate shift) (fourierForcing coordinate N) := by
  rw [fourierPrefix_source coordinate shift nonnegative, fourier_read]

/-- The original zero law consumes the full normalized finite forcing balance.
No individual finite prefix is assigned Pa membership or a zero read. -/
theorem signed_source_tendsto_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    Filter.Tendsto (fun N : ℕ =>
      coefficient (star coordinate.value) N *
        inner ℂ (positionSeed coordinate shift) (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
      coefficient (1 - star coordinate.value) N *
        inner ℂ (fourierSeed coordinate shift)
          (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) +
      inner ℂ (positionSeed coordinate shift) (positionForcing coordinate N) -
      inner ℂ (fourierSeed coordinate shift) (fourierForcing coordinate N)) Filter.atTop (𝓝 0) := by
  have actual := finite_signed_pair_tendsto_zero coordinate zero shift nonnegative bounded
  convert actual using 1
  funext N
  rw [positionPrefix_read coordinate shift nonnegative, fourierPrefix_read coordinate shift nonnegative]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.FiniteForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
