import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProbeCutoffValue

/-! The original Hilbert cutoff exhausts the actual pairing without adding a whole-wave moment. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem originalPhysicalCutoff_pairing (radius : ℝ) (value test : BurnolL2) :
    inner ℂ (originalPhysicalCutoff radius value) test =
      ∫ x : ℝ in symmetricInterval radius, inner ℂ (value x) (test x) := by
  rw [L2.inner_def, ← integral_indicator (measurableSet_symmetricInterval radius)]
  apply integral_congr_ae
  filter_upwards [originalPhysicalCutoff_coeFn radius value] with x read
  rw [read]
  by_cases inside : x ∈ symmetricInterval radius
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside]
  · rw [Set.indicator_of_notMem inside, Set.indicator_of_notMem inside, inner_zero_left]

theorem originalPhysicalCutoff_pairing_tendsto (value test : BurnolL2) :
    Tendsto (fun N : ℕ => inner ℂ (originalPhysicalCutoff (N + 1 : ℝ) value) test) atTop
      (𝓝 (inner ℂ value test)) := by
  let regions := fun N : ℕ => symmetricInterval (N + 1 : ℝ)
  have increasing : Monotone regions := by
    intro i j ij x hx
    have order : (i : ℝ) ≤ j := by exact_mod_cast ij
    change -(i + 1 : ℝ) ≤ x ∧ x ≤ (i + 1 : ℝ) at hx
    change -(j + 1 : ℝ) ≤ x ∧ x ≤ (j + 1 : ℝ)
    constructor <;> linarith [hx.1, hx.2]
  have cover : (⋃ N : ℕ, regions N) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    refine ⟨⌈|x|⌉₊, ?_⟩
    have bound := Nat.le_ceil |x|
    change -((⌈|x|⌉₊ : ℕ) + 1 : ℝ) ≤ x ∧ x ≤ ((⌈|x|⌉₊ : ℕ) + 1 : ℝ)
    exact abs_le.mp (by linarith : |x| ≤ (⌈|x|⌉₊ : ℕ) + 1)
  have generated := tendsto_setIntegral_of_monotone
    (fun N : ℕ => measurableSet_symmetricInterval (N + 1 : ℝ)) increasing
    (L2.integrable_inner (𝕜 := ℂ) value test).integrableOn
  change (⋃ N : ℕ, symmetricInterval (N + 1 : ℝ)) = univ at cover
  rw [cover, Measure.restrict_univ, ← L2.inner_def] at generated
  exact generated.congr (fun N => (originalPhysicalCutoff_pairing (N + 1 : ℝ) value test).symm)

theorem originalPhysicalCutoff_kernel_finite (radius : ℝ) (value : BurnolL2) (N : ℕ)
    (covers : 4 * radius ≤ N) :
    burnolPaSamplingKernel (originalPhysicalCutoff radius value) =
      ∑ n ∈ Finset.range N, burnolAnnulusSamplingL2 (originalPhysicalCutoff radius value) n := by
  unfold burnolPaSamplingKernel
  apply tsum_eq_sum
  intro n outside
  have order : N ≤ n := by
    have excluded : ¬n < N := by simpa only [Finset.mem_range] using outside
    omega
  apply originalPhysicalCutoff_sample_zero
  exact covers.trans (by exact_mod_cast order)

theorem originalPhysicalCutoff_fullPa_transpose (radius : ℝ) (value : BurnolL2) (N : ℕ)
    (covers : 4 * radius ≤ N) (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (originalPhysicalCutoff radius value) (p : BurnolL2) =
      inner ℂ (∑ n ∈ Finset.range N,
        burnolAnnulusSamplingL2 (originalPhysicalCutoff radius value) n) (burnolMobiusSourceL2 p) +
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p *
        star (∫ x : ℝ, originalPhysicalCutoff radius value x) := by
  have generated := burnolPaSamplingKernel_fullPa (originalPhysicalCutoff radius value)
    (originalPhysicalCutoff_integrable radius value) (originalPhysicalCutoff_firstMoment radius value) p inside
  rw [originalPhysicalCutoff_kernel_finite radius value N covers] at generated
  exact generated

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
