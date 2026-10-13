import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientFourierRaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DualLanding

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)

/-- A legitimate almost-everywhere subsequence identifies the independent strong limit
with the finite channel event seen by each nonzero observation. -/
theorem original_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (CountingDual.value coordinate : ℝ → ℂ) =ᵐ[volume] DualSourceRaw.eventRaw coordinate := by
  let sequence := fun N : ℕ => DualSource.source N (burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))
  obtain ⟨indices, strict, pointwise⟩ : ∃ indices : ℕ → ℕ, StrictMono indices ∧
      ∀ᵐ x : ℝ ∂volume, Tendsto (fun n => sequence (indices n) x) atTop
        (𝓝 (CountingDual.value coordinate x)) :=
    (tendstoInMeasure_of_tendsto_Lp (CountingDual.original_dual_tendsto coordinate)).exists_seq_tendsto_ae
  have reads : ∀ᵐ x : ℝ ∂volume, ∀ N : ℕ, sequence N x = DualSourceRaw.raw coordinate N x :=
    ae_all_iff.mpr (DualSourceRaw.original_coeFn coordinate)
  filter_upwards [pointwise, reads, volume.ae_ne (0 : ℝ)] with x converges read nonzero
  have stabilizes : (fun n => sequence (indices n) x) =ᶠ[atTop]
      fun _ => DualSourceRaw.eventRaw coordinate x := by
    filter_upwards [strict.tendsto_atTop.eventually (DualSourceRaw.raw_eventually coordinate x nonzero)]
      with n complete
    rw [read, complete]
  exact tendsto_nhds_unique converges (tendsto_const_nhds.congr' stabilizes.symm)

private theorem eventRaw_outside (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (outside : q < |x|) : DualSourceRaw.eventRaw coordinate x = 0 := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have index : ⌊q / |x|⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one absolute).mpr outside)
  rw [DualSourceRaw.eventRaw, DualSourceRaw.channels, index]
  simp

/-- The independent whole ambient dual actually lands in the original closed q-window. -/
theorem original_support (coordinate : BurnolCompletedMellinCoordinate) :
    CountingDual.value coordinate = burnolQuarterZeroExtension
      (burnolQuarterRestriction (CountingDual.value coordinate)) := by
  have restricted := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (CountingDual.value coordinate))
  apply Lp.ext
  filter_upwards [original_coeFn coordinate,
    burnolQuarterZeroExtension_coe (burnolQuarterRestriction (CountingDual.value coordinate)), restricted]
      with x original extended localRead
  rw [extended]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside]
    exact (localRead inside).symm
  · rw [indicator_of_notMem inside, original]
    exact eventRaw_outside coordinate x (lt_of_not_ge (fun small => inside (abs_le.mp small)))

/-- The same mean functional reads the complete log contact of the independent dual limit. -/
theorem original_mean (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (CountingDual.value coordinate)) =
      2 * inner ℂ SmallScaleLog.logL2 (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) := by
  have continuousMean : Continuous (fun value : BurnolL2 =>
      burnolQuarterMeanCoefficient (burnolQuarterRestriction value)) := by
    unfold burnolQuarterMeanCoefficient
    fun_prop
  have actual := (continuousMean.tendsto (CountingDual.value coordinate)).comp
    (CountingDual.original_dual_tendsto coordinate)
  have constantRead := actual.congr' (show _ =ᶠ[atTop]
      (fun _ : ℕ => 2 * inner ℂ SmallScaleLog.logL2
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) from by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    exact DualSourceRaw.original_mean coordinate N positive)
  exact tendsto_nhds_unique constantRead tendsto_const_nhds

/-- The original Fourier channel samples are exactly the reciprocal samples of the same b. -/
theorem tate_raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolTateReciprocalRaw (AmbientFourierRaw.raw coordinate) x = DualSourceRaw.eventRaw coordinate x := by
  by_cases zero : x = 0
  · simp [zero, burnolTateReciprocalRaw, DualSourceRaw.eventRaw, DualSourceRaw.channels]
  have absolute : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mpr zero).ne'
  have channels : AmbientFourierRaw.channels x⁻¹ = DualSourceRaw.channels x := by
    unfold AmbientFourierRaw.channels DualSourceRaw.channels
    rw [abs_inv]
    congr 2
    ring
  unfold burnolTateReciprocalRaw AmbientFourierRaw.raw
  rw [channels, abs_inv, Complex.ofReal_inv, inv_inv, inv_mul_cancel_left₀ absolute]
  simp only [DualSourceRaw.eventRaw, div_inv_eq_mul]

/-- Independently generated complete dual and original Tate/Fourier source are the same occurrence. -/
theorem original_tate_fourier (coordinate : BurnolCompletedMellinCoordinate) :
    CountingDual.value coordinate = burnolTateReciprocalL2
      (fourierL2 (AmbientCounting.value coordinate)) := by
  let actual := fourierL2 (AmbientCounting.value coordinate)
  have fourierRead : (actual : ℝ → ℂ) =ᵐ[volume] AmbientFourierRaw.raw coordinate :=
    AmbientFourierRaw.original_fourier_coeFn coordinate
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp actual)
    ((Lp.memLp actual).ae_eq fourierRead) fourierRead
  have read := (burnolTateReciprocalL2_coeFn actual).trans pulled
  have original := read.trans (Eventually.of_forall (tate_raw coordinate))
  apply Lp.ext
  exact (original_coeFn coordinate).trans original.symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DualLanding
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
