import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open Filter Set
open scoped Topology

theorem punctured_nonzero_of_imaginary_witness (f : ℂ → ℂ)
    (hm : MeromorphicOn f univ) (ha : AnalyticAt ℂ f Complex.I)
    (hn : f Complex.I ≠ 0) :
    ∃δ : ℝ,0 < δ ∧ ∀z : ℂ,0 < ‖z‖ → ‖z‖ < δ → f z ≠ 0 := by
  have hI : meromorphicOrderAt f Complex.I ≠ ⊤ := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero ha.meromorphicAt).2
    exact nhdsWithin_le_nhds ((ha.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hn)
  have h0 : meromorphicOrderAt f 0 ≠ ⊤ :=
    hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ Complex.I) (mem_univ 0) hI
  have he : ∀ᶠz : ℂ in 𝓝[≠] 0,f z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm 0 (mem_univ 0))).1 h0
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro z hz hzd
  apply hball
  constructor
  · simpa only [Metric.mem_ball,dist_zero_right] using hzd
  · exact (norm_pos_iff.mp hz)

theorem punctured_real_nonzero_of_imaginary_witness (f : ℂ → ℂ)
    (hm : MeromorphicOn f univ) (ha : AnalyticAt ℂ f Complex.I)
    (hn : f Complex.I ≠ 0) :
    ∃δ : ℝ,0 < δ ∧ ∀x : ℝ,0 < |x| → |x| < δ → f x ≠ 0 := by
  obtain ⟨δ,hδ,h⟩ := punctured_nonzero_of_imaginary_witness f hm ha hn
  refine ⟨δ,hδ,?_⟩
  intro x hx hxd
  apply h (x : ℂ)
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using hx
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using hxd

end LowEnergy.ActualFourBlockRealTransfer
