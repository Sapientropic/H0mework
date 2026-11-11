import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCounting
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualShell

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionShell

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalPaPhysicalGreen OriginalRieszFiniteColumns
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem shell_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : shift ≤ Real.log 2) :
    ((originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero)) -
      burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero) : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      bandRaw shift (positionSource coordinate) := by
  let value := PositionCounting.value coordinate zero
  let moved := burnolMultiplicativeDilation (-shift) value
  have read := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_pos (-shift)).ne').ae (PositionCounting.value_coeFn coordinate zero)
  have half : (1 / 2 : ℝ) ≤ Real.exp (-shift) := by
    have source := Real.exp_le_exp.mpr (neg_le_neg bounded)
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using source
  filter_upwards [Lp.coeFn_sub (originalPhysicalCutoff q moved) moved,
    originalPhysicalCutoff_coeFn q moved, burnolMultiplicativeDilation_coeFn (-shift) value, read]
    with x difference cut dilation source
  change value (Real.exp (-shift) * x) = PositionCounting.eventRaw coordinate (Real.exp (-shift) * x) at source
  change (originalPhysicalCutoff q moved - moved : BurnolL2) x = _
  rw [difference, Pi.sub_apply, cut]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, sub_self, bandRaw, if_neg]
    exact fun active => (not_lt_of_ge (abs_le.mpr inside)) active.1
  · have outside : q < |x| := lt_of_not_ge (fun small => inside (abs_le.mp small))
    rw [indicator_of_notMem inside, zero_sub]
    change -burnolMultiplicativeDilation (-shift) value x = _
    rw [dilation, burnolL2RawNormalizedDilation, source]
    have absolute : |Real.exp (-shift) * x| = Real.exp (-shift) * |x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have lower : q / 2 < |Real.exp (-shift) * x| := by
      rw [absolute]
      calc
        q / 2 = (1 / 2 : ℝ) * q := by ring
        _ ≤ Real.exp (-shift) * q := mul_le_mul_of_nonneg_right half (by norm_num)
        _ < Real.exp (-shift) * |x| := mul_lt_mul_of_pos_left outside (Real.exp_pos _)
    have upper : |Real.exp (-shift) * x| ≤ q ↔ |x| ≤ q * Real.exp shift := by
      rw [absolute, Real.exp_neg, ← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos shift)]
    by_cases covered : |Real.exp (-shift) * x| ≤ q
    · rw [PositionCounting.event_collar coordinate _ lower covered, absolute,
        bandRaw, if_pos ⟨outside, upper.mp covered⟩]
      ring
    · rw [PositionCounting.event_outside coordinate _ (lt_of_not_ge covered), mul_zero, neg_zero,
        bandRaw, if_neg (fun active => covered (upper.mpr active.2))]

/-- The zero-generated L² position result supplies the original Pa seed after its actual dilation. -/
theorem original_seed (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    positionSeed coordinate shift =
      originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero)) -
        burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero) := by
  apply ext_inner_left ℂ
  intro test
  rw [positionSeed_pairing coordinate shift nonnegative, L2.inner_def]
  exact integral_congr_ae ((shell_read coordinate zero shift bounded).mono
    (fun x read => congrArg (inner ℂ (test x)) read.symm))

private theorem source_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) (N : ℕ) (test : BurnolL2) :
    inner ℂ (FiniteForcing.source N (positionSeed coordinate shift)) test =
      inner ℂ (FiniteForcing.source N (originalPhysicalCutoff q
        (burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero)))) test -
      inner ℂ (FiniteForcing.source N (PositionCounting.value coordinate zero))
        (burnolMultiplicativeDilation shift test) := by
  rw [original_seed coordinate zero shift nonnegative bounded]
  have linear := map_sub (CountingDual.sourceCLM N)
    (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero)))
    (burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero))
  simp only [CountingDual.sourceCLM_apply] at linear
  rw [linear, inner_sub_left, SeedCounting.source_dilation]
  have moved := (burnolMultiplicativeDilation (-shift)).inner_map_eq_flip
    (FiniteForcing.source N (PositionCounting.value coordinate zero)) test
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at moved
  rw [moved]

/-- The original Pa consumer pays both reads after the genuine position counting output. -/
theorem original_after_counting_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    Tendsto (fun N : ℕ =>
      inner ℂ (FiniteForcing.source N (originalPhysicalCutoff q
        (burnolMultiplicativeDilation (-shift) (PositionCounting.value coordinate zero))))
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
      inner ℂ (FiniteForcing.source N (PositionCounting.value coordinate zero))
        (burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2)))
      atTop (𝓝 0) := by
  have continuous : Continuous (fun value : BurnolL2 =>
      inner ℂ value (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by fun_prop
  have actual := (continuous.tendsto (positionWave coordinate shift)).comp
    (positionPrefix_tendsto coordinate shift)
  rw [positionWave_zero_read coordinate zero shift nonnegative bounded] at actual
  apply actual.congr'
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [← source_pairing coordinate zero shift nonnegative bounded N,
    FiniteForcing.position_read, FiniteForcing.positionPrefix_read coordinate shift nonnegative]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionShell
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
