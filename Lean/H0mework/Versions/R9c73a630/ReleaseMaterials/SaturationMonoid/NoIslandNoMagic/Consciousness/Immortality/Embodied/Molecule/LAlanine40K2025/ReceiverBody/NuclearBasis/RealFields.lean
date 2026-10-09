import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.TranslationEstimate
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement SourceGaussianModel
open MeasureTheory
noncomputable section

theorem real_field_inner (f g : Point → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x : Point, f x * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x left right
  rw [left,right]
  simp only [Real.inner_apply]

theorem real_field_norm_sq (f : Point → ℝ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖^2 = ∫ x : Point, (f x)^2 := by
  rw [← real_inner_self_eq_norm_sq,real_field_inner]
  simp only [pow_two]

theorem real_field_distance_sq (f g : Point → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖^2 = ∫ x : Point, (f x - g x)^2 := by
  rw [← hf.toLp_sub hg,real_field_norm_sq]
  rfl

theorem base_memLp (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) :
    MemLp (orbital terms jet) 2 volume := by
  apply (memLp_two_iff_integrable_sq (orbital_contDiff terms jet 0).continuous.aestronglyMeasurable).mpr
  simpa only [pow_two] using base_pair_integrable terms positive jet jet

theorem shifted_memLp (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) : MemLp (fun x => orbital terms jet (x - d)) 2 volume := by
  have preserving : MeasurePreserving (fun x : Point => x - d) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Point) (-d)
  exact (base_memLp terms positive jet).comp_measurePreserving preserving

def baseField (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) : Lp ℝ 2 (volume : Measure Point) :=
  (base_memLp terms positive jet).toLp (orbital terms jet)

def shiftedField (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) : Lp ℝ 2 (volume : Measure Point) :=
  (shifted_memLp terms positive jet d).toLp (fun x => orbital terms jet (x - d))

theorem shifted_field_distance_sq (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) :
    ‖shiftedField terms positive jet d - baseField terms positive jet‖^2 ≤
      (∑ k : Fin 3, (d k)^2) * gradientEnergy terms jet := by
  rw [shiftedField,baseField,real_field_distance_sq]
  exact translation_square_bound terms positive jet d

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
