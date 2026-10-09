import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.Domination
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel NuclearBasis Filter
open scoped Topology
noncomputable section

theorem finite_family_local_bound {ι : Type} [Fintype ι]
    (f : ι → ℝ → Point) (continuous : ∀ i, Continuous (f i)) (t₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀, ∀ i, ‖f i t‖ ≤ C := by
  let family : ℝ → ι → Point := fun t i => f i t
  have regular : Continuous family := continuous_pi continuous
  refine ⟨‖family t₀‖+1,by positivity,?_⟩
  have close : ∀ᶠ t in 𝓝 t₀, ‖family t‖ < ‖family t₀‖+1 :=
    regular.norm.continuousAt.eventually_lt continuousAt_const (by linarith)
  filter_upwards [close] with t bound
  intro i
  exact (norm_le_pi_norm (family t) i).trans bound.le

theorem pair_motion_local_bound (left right vl vr : ℝ → Point)
    (cl : Continuous left) (cr : Continuous right) (dl : Continuous vl) (dr : Continuous vr) (t₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀,
      ‖left t‖ ≤ C ∧ ‖right t‖ ≤ C ∧ ‖vl t‖ ≤ C ∧ ‖vr t‖ ≤ C := by
  let f : Fin 4 → ℝ → Point := ![left,right,vl,vr]
  have regular : ∀ i, Continuous (f i) := by
    intro i
    fin_cases i
    · exact cl
    · exact cr
    · exact dl
    · exact dr
  obtain ⟨C,positive,bound⟩ := finite_family_local_bound f regular t₀
  refine ⟨C,positive,?_⟩
  filter_upwards [bound] with t h
  exact ⟨h 0,h 1,h 2,h 3⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
