import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandGlobalSource.FlowWindow

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel ContinuousGradient Set Filter ODE
open scoped NNReal Topology
noncomputable section

/-- Compatible Picard windows define a single original-field curve on the whole line. -/
def flow (initial : Point) (t : ℝ) : Point := window initial (‖t‖₊ + 1) t

theorem flow_eq_window (initial : Point) (radius : ℝ≥0) (t : ℝ) (inside : |t| < (radius : ℝ)) :
    flow initial t = window initial radius t := by
  apply windows_agree initial (‖t‖₊ + 1) radius t _ inside
  simp only [NNReal.coe_add, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs]
  linarith

theorem flow_starts (initial : Point) : flow initial 0 = initial := by
  rw [flow_eq_window initial 1 0 (by norm_num), window_starts]

theorem flow_hasDerivAt (initial : Point) (t : ℝ) :
    HasDerivAt (flow initial) (sourceGradient (flow initial t)) t := by
  let radius : ℝ≥0 := ‖t‖₊ + 1
  have inside : |t| < (radius : ℝ) := by
    simp only [radius, NNReal.coe_add, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs]
    linarith
  have interval := abs_lt.mp inside
  have same : flow initial =ᶠ[𝓝 t] window initial radius := by
    filter_upwards [Ioo_mem_nhds interval.1 interval.2] with u hu
    exact flow_eq_window initial radius u (abs_lt.mpr hu)
  rw [flow_eq_window initial radius t inside]
  exact (window_derivative initial radius t interval).congr_of_eventuallyEq same

theorem flow_continuous (initial : Point) : Continuous (flow initial) :=
  continuous_iff_continuousAt.mpr (fun t => (flow_hasDerivAt initial t).continuousAt)

theorem flow_unique (initial : Point) (curve : ℝ → Point)
    (starts : curve 0 = initial)
    (evolves : ∀ t, HasDerivAt curve (sourceGradient (curve t)) t) : curve = flow initial := by
  apply ODE_solution_unique_univ (v := fun _ => sourceGradient) (s := fun _ => univ)
    (fun _ => sourceGradient_globally_lipschitz.lipschitzOnWith)
    (fun t => ⟨evolves t,mem_univ _⟩)
    (fun t => ⟨flow_hasDerivAt initial t,mem_univ _⟩)
  exact starts.trans (flow_starts initial).symm

theorem flow_add (initial : Point) (s t : ℝ) : flow initial (s + t) = flow (flow initial s) t := by
  have same : (fun u => flow initial (s + u)) = flow (flow initial s) := by
    apply flow_unique _ _ (by simp)
    intro u
    have shift : HasDerivAt (fun z : ℝ => s + z) 1 u := by
      simpa using (hasDerivAt_id u).const_add s
    simpa only [Function.comp_def, one_smul] using
      (flow_hasDerivAt initial (s + u)).scomp u shift
  exact congrFun same t

theorem flow_inverse (initial : Point) (t : ℝ) : flow (flow initial t) (-t) = initial := by
  rw [← flow_add, add_neg_cancel, flow_starts]

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
