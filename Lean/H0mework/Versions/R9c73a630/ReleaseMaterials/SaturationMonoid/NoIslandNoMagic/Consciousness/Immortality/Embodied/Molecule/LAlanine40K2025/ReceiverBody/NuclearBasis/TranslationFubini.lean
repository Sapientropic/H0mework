import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.TranslationCalculus

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement SourceGaussianModel
open MeasureTheory
noncomputable section

def unitInterval : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance unitInterval_finite : IsFiniteMeasure unitInterval := by
  unfold unitInterval
  infer_instance

theorem translated_square_integrable (h : Point → ℝ) (regular : Continuous h)
    (square : Integrable (fun x => (h x)^2)) (d : Point) :
    Integrable (fun z : ℝ × Point => (h (linePoint d z.1 z.2))^2) (unitInterval.prod volume) := by
  have joint : Continuous (fun z : ℝ × Point => (h (linePoint d z.1 z.2))^2) :=
    (regular.comp (by unfold linePoint; fun_prop)).pow 2
  apply (integrable_prod_iff joint.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun s => square.comp_sub_right (fun k => s * d k)
  · have fixed (s : ℝ) : (∫ x : Point, ‖(h (linePoint d s x))^2‖) = ∫ x : Point, (h x)^2 := by
      simp only [Real.norm_eq_abs,abs_pow,sq_abs]
      exact integral_sub_right_eq_self (μ := (volume : Measure Point)) (fun x => (h x)^2) (fun k => s * d k)
    simp_rw [fixed]
    exact integrable_const _

theorem translated_time_square_integrable (h : Point → ℝ) (regular : Continuous h)
    (square : Integrable (fun x => (h x)^2)) (d : Point) :
    Integrable (fun x : Point => ∫ t in (0 : ℝ)..1, (h (linePoint d t x))^2) := by
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (translated_square_integrable h regular square d).integral_prod_right

theorem translated_time_square_integral (h : Point → ℝ) (regular : Continuous h)
    (square : Integrable (fun x => (h x)^2)) (d : Point) :
    (∫ x : Point, ∫ t in (0 : ℝ)..1, (h (linePoint d t x))^2) = ∫ x : Point, (h x)^2 := by
  have flip := integral_integral_swap (μ := unitInterval) (ν := (volume : Measure Point))
    (f := fun t x => (h (linePoint d t x))^2) (translated_square_integrable h regular square d)
  have fixed (s : ℝ) : (∫ x : Point, (h (linePoint d s x))^2) = ∫ x : Point, (h x)^2 :=
    integral_sub_right_eq_self (μ := (volume : Measure Point)) (fun x => (h x)^2) (fun k => s * d k)
  change (∫ t : ℝ, ∫ x : Point, (h (linePoint d t x))^2 ∂volume ∂unitInterval) =
    (∫ x : Point, ∫ t : ℝ, (h (linePoint d t x))^2 ∂unitInterval) at flip
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  change (∫ x : Point, ∫ t : ℝ, (h (linePoint d t x))^2 ∂unitInterval) = _
  rw [← flip]
  simp_rw [fixed]
  simp [unitInterval,measureReal_def]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
