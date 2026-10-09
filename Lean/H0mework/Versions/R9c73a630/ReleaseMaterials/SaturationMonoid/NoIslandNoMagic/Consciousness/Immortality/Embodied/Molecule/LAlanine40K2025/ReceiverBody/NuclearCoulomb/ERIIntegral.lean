import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.ERI

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel NuclearBasis
open MeasureTheory Filter
open scoped Topology
noncomputable section

def primitiveERI (terms : Quartet → Term) (jets : Quartet → MultiIndex) (centres : Quartet → Point) : ℝ :=
  ∫ z : Point × Point, eriIntegrand terms jets centres z

theorem eri_motion_local_bound (centres speeds : ℝ → Quartet → Point)
    (hc : Continuous centres) (hv : Continuous speeds) (t₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀, (∀ h, ‖centres t h‖ ≤ C) ∧ ∀ h, ‖speeds t h‖ ≤ C := by
  let family : Quartet ⊕ Quartet → ℝ → Point := fun slot t => match slot with
    | .inl h => centres t h
    | .inr h => speeds t h
  have regular : ∀ slot, Continuous (family slot) := by
    intro slot
    rcases slot with h | h
    · exact (continuous_apply h).comp hc
    · exact (continuous_apply h).comp hv
  obtain ⟨C,positive,bound⟩ := finite_family_local_bound family regular t₀
  refine ⟨C,positive,?_⟩
  filter_upwards [bound] with t h
  exact ⟨fun slot => h (.inl slot),fun slot => h (.inr slot)⟩

theorem primitive_eri_derivative (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (centres speeds : ℝ → Quartet → Point) (regular : Continuous speeds)
    (motion : ∀ t h k, HasDerivAt (fun s => centres s h k) (speeds t h k) t) (t₀ : ℝ) :
    Integrable (eriRate terms jets (centres t₀) (speeds t₀)) ∧
      HasDerivAt (fun t => primitiveERI terms jets (centres t))
        (∫ z : Point × Point, eriRate terms jets (centres t₀) (speeds t₀) z) t₀ := by
  have centresContinuous : Continuous centres := continuous_pi fun h => continuous_pi fun k =>
    continuous_iff_continuousAt.mpr fun t => (motion t h k).continuousAt
  obtain ⟨C,_,near⟩ := eri_motion_local_bound centres speeds centresContinuous regular t₀
  let s : Set ℝ := {t | (∀ h, ‖centres t h‖ ≤ C) ∧ ∀ h, ‖speeds t h‖ ≤ C}
  have neighborhood : s ∈ 𝓝 t₀ := near
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z => eriIntegrand terms jets (centres t) z)
    (F' := fun t z => eriRate terms jets (centres t) (speeds t) z)
    (bound := eriRateEnvelope terms jets C)
    neighborhood
    (Filter.Eventually.of_forall fun t => eri_integrand_measurable terms jets (centres t))
    (eri_integrand_integrable terms positive jets (centres t₀))
    (eri_rate_measurable terms jets (centres t₀) (speeds t₀))
    (Filter.Eventually.of_forall fun z t ht => eri_rate_uniform_bound terms positive jets (centres t) (speeds t) C ht.1 ht.2 z)
    (eri_rate_envelope_integrable terms positive jets C)
    (Filter.Eventually.of_forall fun z t _ => eri_integrand_derivative terms jets centres (speeds t) t z (motion t))

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
