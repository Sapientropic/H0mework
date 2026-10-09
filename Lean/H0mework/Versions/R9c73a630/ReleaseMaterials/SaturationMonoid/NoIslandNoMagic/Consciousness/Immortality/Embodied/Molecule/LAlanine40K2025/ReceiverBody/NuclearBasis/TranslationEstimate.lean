import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.TranslationFubini
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.TranslationEnergy

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement SourceGaussianModel
open MeasureTheory
noncomputable section

theorem translation_square_integrable (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) :
    Integrable (fun x : Point => (orbital terms jet (x - d) - orbital terms jet x)^2) := by
  have majorant := translated_time_square_integrable (directional terms jet d)
    (directional_continuous terms jet d) (directional_square_integrable terms positive jet d) d
  apply majorant.mono'
  · have regular := (orbital_contDiff terms jet 0).continuous
    exact ((regular.comp (continuous_id.sub continuous_const)).sub regular).pow 2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs,abs_pow,sq_abs,line_rate_directional] using! orbital_line_square_le terms jet d x

theorem translation_square_bound (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) :
    (∫ x : Point, (orbital terms jet (x - d) - orbital terms jet x)^2) ≤
      (∑ k : Fin 3, (d k)^2) * gradientEnergy terms jet := by
  have majorant := translated_time_square_integrable (directional terms jet d)
    (directional_continuous terms jet d) (directional_square_integrable terms positive jet d) d
  calc
    _ ≤ ∫ x : Point, ∫ t in (0 : ℝ)..1, (directional terms jet d (linePoint d t x))^2 := by
      apply integral_mono (translation_square_integrable terms positive jet d) majorant
      intro x
      simpa only [line_rate_directional] using orbital_line_square_le terms jet d x
    _ = ∫ x : Point, (directional terms jet d x)^2 :=
      translated_time_square_integral _ (directional_continuous terms jet d)
        (directional_square_integrable terms positive jet d) d
    _ ≤ _ := directional_energy_bound terms positive jet d

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
