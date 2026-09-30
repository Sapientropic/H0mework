import H0mework.Chemistry.LAlanineBoundary.CalculusAdjugate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary.Calculus

noncomputable section
open scoped BigOperators

def pullback (f g : Space → Space) (p : Space) : Space :=
  (jacobian f p).adjugate.mulVec (g (f p))

theorem pullback_contDiff (f g : Space → Space) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (pullback f g) := by
  apply contDiff_pi.mpr
  intro i
  have hc := adjugate_contDiff f hf i
  have hfg : ContDiff ℝ 1 (fun p => g (f p)) := hg.comp (hf.of_le (by norm_num))
  change ContDiff ℝ 1 (fun p => ∑ k : Fin 3, (jacobian f p).adjugate i k * g (f p) k)
  exact ContDiff.sum (fun k _ => (hc k).mul (contDiff_pi.mp hfg k))

theorem pullback_partial (f g : Space → Space) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (p : Space) (i : Fin 3) :
    dcoord (fun x => pullback f g x i) i p =
      ∑ k : Fin 3, (dcoord (fun x => (jacobian f x).adjugate i k) i p * g (f p) k +
        (jacobian f p).adjugate i k *
          ∑ j : Fin 3, jacobian g (f p) k j * jacobian f p j i) := by
  have hc (k : Fin 3) : Differentiable ℝ (fun x => (jacobian f x).adjugate i k) :=
    (adjugate_contDiff f hf i k).differentiable (by norm_num)
  have hfg (k : Fin 3) : Differentiable ℝ (fun x => g (f x) k) :=
    (contDiff_pi.mp (hg.comp (hf.of_le (by norm_num))) k).differentiable (by norm_num)
  change dcoord (fun x => ∑ k : Fin 3, (jacobian f x).adjugate i k * g (f x) k) i p = _
  rw [partial_sum _ (fun k => (hc k).fun_mul (hfg k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [partial_mul _ _ (hc k) (hfg k),
    partial_comp f g (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]

/-- Polynomial Piola pullback; invertibility or a preinstalled divergence law is not needed. -/
theorem div_pullback (f g : Space → Space) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (p : Space) :
    (∑ i : Fin 3, fderiv ℝ (pullback f g) p (unit i) i) =
      (jacobian f p).det * ∑ i : Fin 3, jacobian g (f p) i i := by
  have hd : Differentiable ℝ (pullback f g) := (pullback_contDiff f g hf hg).differentiable (by norm_num)
  change (∑ i : Fin 3, jacobian (pullback f g) p i i) = _
  simp_rw [jacobian_eq_dcoord _ hd, pullback_partial f g hf hg, Finset.sum_add_distrib]
  have cancel : (∑ i : Fin 3, ∑ k : Fin 3,
      dcoord (fun x => (jacobian f x).adjugate i k) i p * g (f p) k) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, adjugate_divergence f hf]
    simp
  rw [cancel, zero_add]
  simpa only [Finset.mul_sum, mul_assoc] using adjugate_trace_contraction (jacobian f p) (jacobian g (f p))

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary.Calculus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
