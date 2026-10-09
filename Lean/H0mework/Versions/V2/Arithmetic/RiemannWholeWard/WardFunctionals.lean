import H0mework.Versions.V2.Arithmetic.RiemannWholeWard.WindowReadback

/-! The finite source Ward is an equation between continuous reads of one original Pa value. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem grid_positive (n : ℕ) (positive : 0 < n) (j : ℕ) :
    0 < reciprocalSampleGrid n j := by
  cases j with
  | zero => norm_num
  | succ j =>
    rw [reciprocal_sample_grid_succ]
    exact div_pos (by exact_mod_cast positive) (by positivity)

def fullPaContactLoad (coordinate : BurnolCompletedMellinCoordinate)
    (n : ℕ) (positive : 0 < n) : burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] ℂ :=
  let embedding := burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL
  (-reciprocalSampleWave coordinate.value n (4 * n - 1) (1 / 4)) •
      ((secondContactFlux coordinate (1 / 4) (by norm_num)).comp embedding) +
    reciprocalSampleFlux coordinate.value n (4 * n - 1) (1 / 4) •
      ((secondContact coordinate (1 / 4) (by norm_num)).comp embedding) +
    (2 * coordinate.value - 1) • (∑ j ∈ Finset.range (reciprocalSampleGridLength n - 1),
      ((n / 4 + j + 1 : ℕ) : ℂ)⁻¹ •
        ((secondContact coordinate (reciprocalSampleGrid n (j + 1))
          (grid_positive n positive (j + 1))).comp embedding)) -
    (2 * coordinate.value - 1) •
      (contactReciprocalIntegral.comp (sourceSecondWindow coordinate))

theorem fullPaContactLoad_compact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource)
    (inside : burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompactAdditivePhysicalState source) = burnolCompactAdditivePhysicalState source)
    (n : ℕ) (positive : 0 < n) :
    fullPaContactLoad coordinate n positive ⟨burnolCompactAdditivePhysicalState source, inside⟩ =
      sourceReciprocalContactLoad coordinate source n := by
  let p := burnolCompactAdditivePhysicalState source
  have atInner : (1 / 4 : ℝ) ∈ Icc (1 / 4) 4 := by constructor <;> norm_num
  have contacts : (∑ j ∈ Finset.range (reciprocalSampleGridLength n - 1),
      ((n / 4 + j + 1 : ℕ) : ℂ)⁻¹ * secondContact coordinate (reciprocalSampleGrid n (j + 1))
        (grid_positive n positive (j + 1)) p) =
      ∑ j ∈ Finset.range (reciprocalSampleGridLength n - 1),
        secondCoefficient coordinate source (reciprocalSampleGrid n (j + 1)) /
          ((n / 4 + j + 1 : ℕ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have bounded : j + 1 ≤ reciprocalSampleGridLength n := by
      have := Finset.mem_range.mp hj
      omega
    rw [secondContact_compact coordinate source fixed (reciprocal_sample_grid_bounds n positive bounded)]
    ring
  simp only [fullPaContactLoad, add_apply, sub_apply, smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  change -reciprocalSampleWave coordinate.value n (4 * n - 1) (1 / 4) *
      secondContactFlux coordinate (1 / 4) (by norm_num) p +
    reciprocalSampleFlux coordinate.value n (4 * n - 1) (1 / 4) *
      secondContact coordinate (1 / 4) (by norm_num) p +
    (2 * coordinate.value - 1) *
      (∑ j ∈ Finset.range (reciprocalSampleGridLength n - 1),
        ((n / 4 + j + 1 : ℕ) : ℂ)⁻¹ * secondContact coordinate (reciprocalSampleGrid n (j + 1))
          (grid_positive n positive (j + 1)) p) -
    (2 * coordinate.value - 1) * contactReciprocalIntegral
      (sourceSecondWindow coordinate ⟨p, inside⟩) = _
  rw [contacts, secondContactFlux_compact coordinate source fixed atInner,
    secondContact_compact coordinate source fixed atInner,
    (sourceSecondWindow_compact_integrals coordinate source fixed).2]
  unfold sourceReciprocalContactLoad reciprocalGreenCurrent
  ring

def originalFiniteSourceWard {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) :
    burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] ℂ :=
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  (∑ n ∈ Finset.range N, fullPaContactLoad coordinate (n + 1) (by omega)) +
    ((1 / 2 : ℂ) * ∫ x : ℝ, W x) • ((secondContactFlux coordinate (1 / 4) (by norm_num)).comp
      burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL) +
    ((2 * observation.coordinate - 1) / 2) • (contactIntegral.comp (sourceSecondWindow coordinate))

theorem originalFiniteSourceWard_compact {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ)
    (source : burnolCompactAnnulusSource)
    (inside : burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompactAdditivePhysicalState source) = burnolCompactAdditivePhysicalState source) :
    4 * contactBilinearRead (originalFiniteContactKernel observation nontrivial rightHalf N)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source))) =
        originalFiniteSourceWard observation nontrivial rightHalf N
          ⟨burnolCompactAdditivePhysicalState source, inside⟩ := by
  have generated := original_W_complete_mean_ward observation nontrivial rightHalf source N
  rw [originalFiniteContactKernel_compact_read observation nontrivial rightHalf N source]
  rw [generated]
  simp only [originalFiniteSourceWard, sum_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, Submodule.subtypeL_apply]
  simp_rw [fullPaContactLoad_compact (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) source inside fixed,
    secondContactFlux_compact (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) source fixed (show (1 / 4 : ℝ) ∈ Icc (1 / 4) 4 by
      constructor <;> norm_num),
    (sourceSecondWindow_compact_integrals (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) source fixed).1]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
