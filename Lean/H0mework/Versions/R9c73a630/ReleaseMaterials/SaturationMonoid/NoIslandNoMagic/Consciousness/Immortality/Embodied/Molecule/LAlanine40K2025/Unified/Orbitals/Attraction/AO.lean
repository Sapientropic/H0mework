import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Primitive
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coulomb

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025 UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource SourceCoulomb MeasureTheory
noncomputable section

def aoAttractionFinite (i j : Basis) (C : Fin 3 → ℚ) : ℝ :=
  ((sourceTerms i).map fun s =>
    ((sourceTerms j).map fun t => primitiveAttraction s t C).sum).sum

private theorem term_pair_kernel_integrable (s t : Term)
    (hs : 0 < s.exponent) (ht : 0 < t.exponent) (C : Fin 3 → ℚ) :
    Integrable (fun x : Point => value s zeroJet x * value t zeroJet x *
      kernel (x - fun k => (C k : ℝ))) := by
  have product : Integrable (fun x : Point => value s zeroJet x * value t zeroJet x) := by
    have h := (term_integrable t ht zeroJet).bdd_mul
      (value_contDiff s zeroJet 0).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (term_uniform_bound s hs zeroJet))
    simpa only [mul_comm] using h
  apply integrable_mul_shifted_kernel _ product
    ((termBound s zeroJet : ℝ) * termBound t zeroJet)
  intro x
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (term_uniform_bound s hs zeroJet x)
    (term_uniform_bound t ht zeroJet x) (abs_nonneg _) (by positivity)

private theorem integrable_list_sum {α : Type*} (items : List α)
    (f : α → Point → ℝ) (each : ∀ item ∈ items, Integrable (f item)) :
    Integrable (fun x : Point => (items.map fun item => f item x).sum) := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have tail : ∀ next ∈ rest, Integrable (f next) := by
      intro next member
      exact each next (by simp [member])
    change Integrable (f item + fun x : Point =>
      (rest.map fun next => f next x).sum)
    exact (each item (by simp)).add (ih tail)

private theorem integral_list_sum {α : Type*} (items : List α)
    (f : α → Point → ℝ) (each : ∀ item ∈ items, Integrable (f item)) :
    (∫ x : Point, (items.map fun item => f item x).sum) =
      (items.map fun item => ∫ x : Point, f item x).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have tail : ∀ next ∈ rest, Integrable (f next) := by
      intro next member
      exact each next (by simp [member])
    have restIntegrable := integrable_list_sum rest f tail
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (each item (by simp)) restIntegrable, ih tail]

private theorem double_list_sum {α β : Type*} (left : List α) (right : List β)
    (f : α → ℝ) (g : β → ℝ) (scale : ℝ) :
    (left.map f).sum * (right.map g).sum * scale =
      (left.map fun a => (right.map fun b => f a * g b * scale).sum).sum := by
  have each (a : α) : f a * (right.map g).sum * scale =
      (right.map fun b => f a * g b * scale).sum := by
    induction right with
    | nil => simp
    | cons b rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring
  induction left with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← each a, ← ih]
    ring

theorem ao_attraction_finite (i j : Basis) (C : Fin 3 → ℚ) :
    (∫ x : Point, ao i x * ao j x * kernel (x - fun k => (C k : ℝ))) =
      aoAttractionFinite i j C := by
  let P := sourceTerms i
  let Q := sourceTerms j
  let F : Term → Term → Point → ℝ := fun s t x =>
    value s zeroJet x * value t zeroJet x *
      kernel (x - fun k => (C k : ℝ))
  have each (s : Term) (hs : s ∈ P) (t : Term) (ht : t ∈ Q) :
      Integrable (F s t) :=
    term_pair_kernel_integrable s t
      (source_exponents_positive i s hs)
      (source_exponents_positive j t ht) C
  have inner (s : Term) (hs : s ∈ P) :
      (∫ x : Point, (Q.map fun t => F s t x).sum) =
        (Q.map fun t => ∫ x : Point, F s t x).sum :=
    integral_list_sum Q (F s) (fun t ht => each s hs t ht)
  have innerIntegrable (s : Term) (hs : s ∈ P) :
      Integrable (fun x : Point => (Q.map fun t => F s t x).sum) := by
    exact integrable_list_sum Q (F s) (fun t ht => each s hs t ht)
  have pointwise (x : Point) :
      ao i x * ao j x * kernel (x - fun k => (C k : ℝ)) =
      (P.map fun s => (Q.map fun t => F s t x).sum).sum := by
    change (P.map fun s => value s zeroJet x).sum *
      (Q.map fun t => value t zeroJet x).sum * _ = _
    exact double_list_sum P Q (fun s => value s zeroJet x)
      (fun t => value t zeroJet x) _
  calc
    (∫ x : Point, ao i x * ao j x * kernel (x - fun k => (C k : ℝ))) =
        ∫ x : Point, (P.map fun s => (Q.map fun t => F s t x).sum).sum := by
          congr 1
          funext x
          exact pointwise x
    _ = (P.map fun s => ∫ x : Point,
        (Q.map fun t => F s t x).sum).sum :=
          integral_list_sum P _ innerIntegrable
    _ = (P.map fun s => (Q.map fun t =>
        ∫ x : Point, F s t x).sum).sum := by
          congr 1
          apply List.map_congr_left
          intro s hs
          exact inner s hs
    _ = aoAttractionFinite i j C := by
          unfold aoAttractionFinite
          congr 1
          apply List.map_congr_left
          intro s hs
          congr 1
          apply List.map_congr_left
          intro t ht
          exact primitive_attraction_closed s t
            (source_exponents_positive i s hs)
            (source_exponents_positive j t ht) C

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
