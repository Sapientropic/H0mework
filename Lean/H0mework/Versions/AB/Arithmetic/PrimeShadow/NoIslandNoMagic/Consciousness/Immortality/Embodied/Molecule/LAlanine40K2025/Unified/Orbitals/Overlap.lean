import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Terms

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement GaussianPrimitive SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource
open MeasureTheory
noncomputable section

private theorem term_orbital_integrable (term : Term) (terms : List Term)
    (ht : 0 < term.exponent) (hs : ∀ s ∈ terms, 0 < s.exponent) :
    Integrable (fun x => value term zeroJet x * orbital terms zeroJet x) :=
  (orbital_integrable terms hs zeroJet).bdd_mul
    (value_contDiff term zeroJet 0).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => term_uniform_bound term ht zeroJet x))

private theorem orbitals_product_integrable (left right : List Term)
    (hl : ∀ t ∈ left, 0 < t.exponent) (hr : ∀ t ∈ right, 0 < t.exponent) :
    Integrable (fun x => orbital left zeroJet x * orbital right zeroJet x) :=
  (orbital_integrable right hr zeroJet).bdd_mul
    (orbital_contDiff left zeroJet 0).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => orbital_uniform_bound left hl zeroJet x))

def termOverlapProgram (first : Term) (right : List Term) : ℝ :=
  (right.map (termOverlap first)).sum

def overlapProgram (left right : List Term) : ℝ :=
  (left.map (fun first => termOverlapProgram first right)).sum

private theorem term_program_correct (first : Term) (right : List Term)
    (hf : 0 < first.exponent) (hr : ∀ t ∈ right, 0 < t.exponent) :
    (∫ x : Point, value first zeroJet x * orbital right zeroJet x) = termOverlapProgram first right := by
  induction right with
  | nil => simp [orbital,termOverlapProgram]
  | cons second rest ih =>
      have hs := hr second (by simp)
      have restPositive : ∀ t ∈ rest, 0 < t.exponent := fun t ht => hr t (by simp [ht])
      have hp : Integrable (fun x => value first zeroJet x * value second zeroJet x) :=
        (term_integrable second hs zeroJet).bdd_mul
          (value_contDiff first zeroJet 0).continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => term_uniform_bound first hf zeroJet x))
      have same : (fun x => value first zeroJet x * orbital (second::rest) zeroJet x) =
          fun x => value first zeroJet x * value second zeroJet x + value first zeroJet x * orbital rest zeroJet x := by
        funext x
        simp only [orbital,List.map_cons,List.sum_cons,mul_add]
      rw [same,integral_add hp (term_orbital_integrable first rest hf restPositive),
        term_overlap_evaluated first second (add_pos hf hs), ih restPositive]
      rfl

theorem overlap_program_correct (left right : List Term)
    (hl : ∀ t ∈ left, 0 < t.exponent) (hr : ∀ t ∈ right, 0 < t.exponent) :
    (∫ x : Point, orbital left zeroJet x * orbital right zeroJet x) = overlapProgram left right := by
  induction left with
  | nil => simp [orbital,overlapProgram]
  | cons first rest ih =>
      have hf := hl first (by simp)
      have restPositive : ∀ t ∈ rest, 0 < t.exponent := fun t ht => hl t (by simp [ht])
      have same : (fun x => orbital (first::rest) zeroJet x * orbital right zeroJet x) =
          fun x => value first zeroJet x * orbital right zeroJet x + orbital rest zeroJet x * orbital right zeroJet x := by
        funext x
        simp only [orbital,List.map_cons,List.sum_cons,add_mul]
      rw [same,integral_add (term_orbital_integrable first right hf hr)
        (orbitals_product_integrable rest right restPositive hr),
        term_program_correct first right hf hr,ih restPositive]
      rfl

/-- Every entry is computed from the original 208 Gaussian terms, rather than supplied by an overlap matrix. -/
theorem original_overlap_evaluated (b c : Basis) :
    overlap b c = overlapProgram (sourceTerms b) (sourceTerms c) :=
  overlap_program_correct _ _ (source_exponents_positive b) (source_exponents_positive c)

end
end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
