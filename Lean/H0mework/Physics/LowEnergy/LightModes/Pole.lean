import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A generated simple source root gives a genuine punctured inverse domain
and its nonzero residue, rather than only a zero of a truncated symbol. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
open Filter Topology
noncomputable section

theorem simple_zero_punctured (f : ℂ → ℂ) (point derivative : ℂ)
    (hasDerivative : HasDerivAt f derivative point) (root : f point=0) (simple : derivative≠0) :
    ∀ᶠ z in 𝓝[≠] point, f z≠0 := by
  have slopeNonzero := hasDerivative.tendsto_slope.eventually (eventually_ne_nhds simple)
  filter_upwards [slopeNonzero] with z nonzero
  intro zero
  apply nonzero
  simp [slope,root,zero]

theorem simple_pole_residue (f g : ℂ → ℂ) (point derivative : ℂ)
    (hasDerivative : HasDerivAt f derivative point) (root : f point=0) (simple : derivative≠0)
    (continuousNumerator : ContinuousAt g point) :
    Tendsto (fun z => (z-point)*(g z/f z)) (𝓝[≠] point) (𝓝 (g point/derivative)) := by
  have numerator := continuousNumerator.tendsto.mono_left (show 𝓝[≠] point≤𝓝 point from inf_le_left)
  have generated := numerator.div hasDerivative.tendsto_slope simple
  convert! generated using 1
  funext z
  change (z-point)*(g z/f z)=g z/(slope f point z)
  simp only [slope,root,vsub_eq_sub,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem source_pole_nonzero (f g : ℂ → ℂ) (point derivative : ℂ)
    (hasDerivative : HasDerivAt f derivative point) (root : f point=0) (simple : derivative≠0)
    (continuousNumerator : ContinuousAt g point) (visible : g point≠0) :
    Tendsto (fun z => (z-point)*(g z/f z)) (𝓝[≠] point) (𝓝 (g point/derivative)) ∧
      g point/derivative≠0 ∧ (∀ᶠ z in 𝓝[≠] point, f z≠0) :=
  ⟨simple_pole_residue f g point derivative hasDerivative root simple continuousNumerator,
    div_ne_zero visible simple,simple_zero_punctured f point derivative hasDerivative root simple⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
