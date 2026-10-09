import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.Identity
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.Cutoff
import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Integrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource GlobalSource.Differential Set MeasureTheory Filter
open scoped Topology
noncomputable section

def cutoffDivergence (n : ℕ) (x : Point) : ℝ :=
  laplacian sourceTerms densityMatrix x*(cutoff n).value x+(cutoff n).derivative x (sourceGradient x)

theorem cutoffDivergence_continuous (n : ℕ) : Continuous (cutoffDivergence n) :=
  ((laplacian_contDiff sourceTerms densityMatrix 0).continuous.mul (cutoff n).smooth.continuous).add
    ((cutoff n).derivative_continuous.clm_apply (sourceGradient_contDiff 0).continuous)

theorem cutoffDivergence_integral (n : ℕ) : (∫ x in basin, cutoffDivergence n x) = 0 :=
  original_weak_divergence (cutoff n)

theorem cutoff_gradient_limit (C : ℝ) (bound : ∀ n x, ‖(cutoff n).derivative x‖ ≤ cutoffScale n*C) (x : Point) :
    Tendsto (fun n => (cutoff n).derivative x (sourceGradient x)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ((cutoff n).derivative x).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_right (bound n x) (norm_nonneg _)))
  simpa only [zero_mul] using (cutoffScale_tends_zero.mul_const C).mul_const ‖sourceGradient x‖

theorem cutoffDivergence_bound (C : ℝ) (nonnegative : 0 ≤ C)
    (bound : ∀ n x, ‖(cutoff n).derivative x‖ ≤ cutoffScale n*C) (n : ℕ) (x : Point) :
    ‖cutoffDivergence n x‖ ≤ ‖laplacian sourceTerms densityMatrix x‖+C*‖sourceGradient x‖ := by
  have value : ‖(cutoff n).value x‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_range n x).1]
    exact (cutoff_range n x).2
  have derivative : ‖(cutoff n).derivative x (sourceGradient x)‖ ≤ C*‖sourceGradient x‖ := by
    apply ((cutoff n).derivative x).le_opNorm _ |>.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (bound n x).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutoffScale_le_one n) nonnegative)
  calc
    _ ≤ ‖laplacian sourceTerms densityMatrix x*(cutoff n).value x‖+
        ‖(cutoff n).derivative x (sourceGradient x)‖ := norm_add_le _ _
    _ ≤ ‖laplacian sourceTerms densityMatrix x‖+C*‖sourceGradient x‖ := by
      apply add_le_add _ derivative
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left value (norm_nonneg _)).trans_eq (mul_one _)

/-- The original basin pays its integrated zero-flux law through actual invariant transport and source L1 decay. -/
theorem actual_basin_zero_flux : (∫ x in basin, laplacian sourceTerms densityMatrix x) = 0 := by
  obtain ⟨C,nonnegative,bound⟩ := cutoff_derivative_bounds
  have converges : Tendsto (fun n => ∫ x in basin, cutoffDivergence n x) atTop
      (𝓝 (∫ x in basin, laplacian sourceTerms densityMatrix x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖laplacian sourceTerms densityMatrix x‖+C*‖sourceGradient x‖)
      (fun n => (cutoffDivergence_continuous n).aestronglyMeasurable)
      (sourceLaplacian_integrable.norm.add (sourceGradient_integrable.norm.const_mul C)).integrableOn
      (fun n => Eventually.of_forall (cutoffDivergence_bound C nonnegative bound n))
    apply Eventually.of_forall
    intro x
    have first : Tendsto (fun _ : ℕ => laplacian sourceTerms densityMatrix x) atTop
        (𝓝 (laplacian sourceTerms densityMatrix x)) := tendsto_const_nhds
    have limit := (first.mul (cutoff_tends_one x)).add (cutoff_gradient_limit C bound x)
    simpa only [cutoffDivergence,mul_one,add_zero] using limit
  simp_rw [cutoffDivergence_integral] at converges
  exact tendsto_nhds_unique converges tendsto_const_nhds

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
