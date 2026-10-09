import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.AttractionRate

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel GlobalSource NuclearBasis
open MeasureTheory Filter
open scoped Topology
noncomputable section

def primitiveAttraction (left right : Term) (l r : MultiIndex) (cl cr : Point) : ℝ :=
  ∫ x : Point, attractionIntegrand left right l r cl cr x

theorem attraction_integrand_integrable (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (cl cr : Point) : Integrable (attractionIntegrand left right l r cl cr) := by
  apply SourceCoulomb.integrable_mul_kernel _ (centred_product_integrable left right hl hr l r cl cr)
    ((termBound left l : ℝ) * (termBound right r : ℝ))
  intro x
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact mul_le_mul (centred_bound left hl l cl x) (centred_bound right hr r cr x)
    (abs_nonneg _) (termBound left l).coe_nonneg

theorem primitive_attraction_derivative (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (cl cr vl vr : ℝ → Point) (vlContinuous : Continuous vl) (vrContinuous : Continuous vr)
    (dl : ∀ t k, HasDerivAt (fun s => cl s k) (vl t k) t)
    (dr : ∀ t k, HasDerivAt (fun s => cr s k) (vr t k) t) (t₀ : ℝ) :
    Integrable (attractionRate left right l r (cl t₀) (cr t₀) (vl t₀) (vr t₀)) ∧
      HasDerivAt (fun t => primitiveAttraction left right l r (cl t) (cr t))
        (∫ x : Point, attractionRate left right l r (cl t₀) (cr t₀) (vl t₀) (vr t₀) x) t₀ := by
  have clContinuous : Continuous cl := continuous_pi fun k =>
    continuous_iff_continuousAt.mpr fun t => (dl t k).continuousAt
  have crContinuous : Continuous cr := continuous_pi fun k =>
    continuous_iff_continuousAt.mpr fun t => (dr t k).continuousAt
  obtain ⟨C,_,near⟩ := pair_motion_local_bound cl cr vl vr clContinuous crContinuous vlContinuous vrContinuous t₀
  let s : Set ℝ := {t | ‖cl t‖ ≤ C ∧ ‖cr t‖ ≤ C ∧ ‖vl t‖ ≤ C ∧ ‖vr t‖ ≤ C}
  have neighborhood : s ∈ 𝓝 t₀ := near
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => attractionIntegrand left right l r (cl t) (cr t) x)
    (F' := fun t x => attractionRate left right l r (cl t) (cr t) (vl t) (vr t) x)
    (bound := attractionRateEnvelope left right l r C)
    neighborhood
    (Filter.Eventually.of_forall fun t => attraction_integrand_measurable left right l r (cl t) (cr t))
    (attraction_integrand_integrable left right hl hr l r (cl t₀) (cr t₀))
    (attraction_rate_measurable left right l r (cl t₀) (cr t₀) (vl t₀) (vr t₀))
    (Filter.Eventually.of_forall fun x t ht => attraction_rate_uniform_bound left right hl hr l r C
      (cl t) (cr t) (vl t) (vr t) x ht.1 ht.2.1 ht.2.2.1 ht.2.2.2)
    (attraction_rate_envelope_integrable left right hl hr l r C)
    (Filter.Eventually.of_forall fun x t _ => attraction_integrand_derivative left right l r cl cr
      (vl t) (vr t) t x (dl t) (dr t))

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
