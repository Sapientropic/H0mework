import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Primitive
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Rows
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coefficients

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Kinetic
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
  GlobalSource
open MeasureTheory
open scoped BigOperators
noncomputable section

variable {α β : Type*}

private theorem list_map_sum_add (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.map_cons,
        List.sum_cons, List.sum_cons, ih]
      ring

/-- Double list sums commute. -/
private theorem list_sum_swap (l : List α) (m : List β) (f : α → β → ℝ) :
    (l.map fun x => (m.map fun y => f x y).sum).sum =
      (m.map fun y => (l.map fun x => f x y).sum).sum := by
  induction m with
  | nil => simp
  | cons b rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have push : (l.map fun x => f x b + (rest.map (f x)).sum).sum =
          (l.map (f · b)).sum + (l.map fun x => (rest.map (f x)).sum).sum :=
        list_map_sum_add l (fun x => f x b) (fun x => (rest.map (f x)).sum)
      rw [push, ih]

/-- flatMap-then-sum equals the list of inner sums. -/
private theorem flatMap_sum {M : Type*} [AddCommMonoid M] (l : List α)
    (f : α → List M) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.flatMap_cons, List.sum_append, List.map_cons,
        List.sum_cons, ih]

private theorem map_flatMap {gγ : Type*} (l : List α) (f : α → List β)
    (g : β → gγ) :
    (l.flatMap f).map g = l.flatMap fun x => (f x).map g := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.flatMap_cons, List.map_append, ih]

private theorem rat_cast_list_sum (l : List ℚ) :
    ((l.map fun q : ℚ => (q : ℝ)).sum : ℝ) = (l.sum : ℝ) := by
  induction l with
  | nil => simp
  | cons q rest ih =>
      rw [List.map_cons, List.sum_cons, ih, List.sum_cons, Rat.cast_add]

/-- Finset sums commute with list sums. -/
private theorem list_map_finset_sum (l : List α) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : α → ι → ℝ) :
    (l.map fun x => ∑ i ∈ s, f x i).sum = ∑ i ∈ s, (l.map (f · i)).sum := by
  induction s using Finset.induction with
  | empty => simp
  | insert x s' hx ih =>
      simp only [Finset.sum_insert hx]
      rw [list_map_sum_add, ih]

/-- The kinetic coefficient is the rational weight of the differentiated
    primitive pair against their shared radial kernel. -/
def kineticCoefficient (first second : Term) : ℚ :=
  (1/2 : ℚ) * ∑ a : Fin 3,
    ((derivativeTerms first a).flatMap fun u =>
      (derivativeTerms second a).map fun v => primitiveCoefficient u v).sum

/-- Per-axis derivative overlap sum reduces to the shared radial kernel. -/
theorem kinetic_pair_axis (t1 t2 : Term) (a : Fin 3) :
    ((derivativeTerms t1 a).flatMap fun u =>
        (derivativeTerms t2 a).map fun v => termOverlap u v).sum =
      ((((derivativeTerms t1 a).flatMap fun u =>
          (derivativeTerms t2 a).map fun v => primitiveCoefficient u v).sum : ℚ) : ℝ) *
      radialKernel (pairExponent t1 t2) (pairPenalty t1 t2) := by
  have inner (u : Term) (hu : u ∈ derivativeTerms t1 a) :
      ((derivativeTerms t2 a).map fun v => termOverlap u v).sum =
        (((derivativeTerms t2 a).map fun v => (primitiveCoefficient u v : ℝ)).sum) *
          radialKernel (pairExponent t1 t2) (pairPenalty t1 t2) := by
    rw [← List.sum_map_mul_right]
    apply congrArg List.sum
    apply List.map_congr_left
    intro v hv
    rw [term_computed_radial]
    rcases derivative_terms_same_radial t1 t2 a u hu v hv with ⟨pe, pp⟩
    rw [pe, pp]
  rw [flatMap_sum]
  conv_rhs => rw [flatMap_sum, ← rat_cast_list_sum, List.map_map]
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  simp only [Function.comp_def]
  rw [← rat_cast_list_sum]
  exact inner u hu

/-- Half the axis sum equals the descriptor coefficient times the kernel. -/
theorem kinetic_pair_descriptor (t1 t2 : Term) :
    (1/2 : ℝ) * ∑ a : Fin 3,
        ((derivativeTerms t1 a).flatMap fun u =>
          (derivativeTerms t2 a).map fun v => termOverlap u v).sum =
      (kineticCoefficient t1 t2 : ℝ) *
        radialKernel (pairExponent t1 t2) (pairPenalty t1 t2) := by
  simp only [kinetic_pair_axis]
  rw [Finset.mul_sum]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  rw [← Rat.cast_sum]
  have half : (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) := by norm_num
  rw [half, ← Rat.cast_mul]
  rfl

/-- Derivative terms of source primitives keep positive exponents. -/
theorem derivative_flatmap_positive (b : Basis) (a : Fin 3) :
    ∀ u ∈ (sourceTerms b).flatMap (derivativeTerms · a), 0 < u.exponent := by
  intro u hu
  rw [List.mem_flatMap] at hu
  rcases hu with ⟨t, ht, hu⟩
  rcases derivative_terms_same_fields t a u hu with ⟨ue, _⟩
  rw [ue]
  exact source_exponents_positive b t ht

def kineticDescriptor (first second : Term) : Descriptor :=
  (kineticCoefficient first second,pairExponent first second,pairPenalty first second)

noncomputable def kineticDescriptors (b c : Basis) : List Descriptor :=
  (sourceTerms b).flatMap fun first =>
    (sourceTerms c).map (kineticDescriptor first)

/-- The kinetic matrix element evaluates to its descriptor list. -/
theorem kinetic_descriptors_evaluated (b c : Basis) :
    kinetic b c = ((kineticDescriptors b c).map descriptorValue).sum := by
  have axis (a : Fin 3) :
      (∫ x : Point, derivative b a x * derivative c a x) =
        overlapProgram ((sourceTerms b).flatMap (derivativeTerms · a))
          ((sourceTerms c).flatMap (derivativeTerms · a)) := by
    have hb := orbital_raise_eq (sourceTerms b) a
    have hc := orbital_raise_eq (sourceTerms c) a
    rw [show (fun x : Point => derivative b a x * derivative c a x) =
        (fun x : Point =>
          orbital ((sourceTerms b).flatMap (derivativeTerms · a)) zeroJet x *
            orbital ((sourceTerms c).flatMap (derivativeTerms · a)) zeroJet x)
      from funext fun x => by
        have e1 : derivative b a x =
            orbital ((sourceTerms b).flatMap (derivativeTerms · a)) zeroJet x :=
          hb x
        have e2 : derivative c a x =
            orbital ((sourceTerms c).flatMap (derivativeTerms · a)) zeroJet x :=
          hc x
        rw [e1, e2]]
    exact overlap_program_correct _ _
      (derivative_flatmap_positive b a) (derivative_flatmap_positive c a)
  have axisProgram (a : Fin 3) :
      overlapProgram ((sourceTerms b).flatMap (derivativeTerms · a))
          ((sourceTerms c).flatMap (derivativeTerms · a)) =
        ((sourceTerms b).flatMap fun t1 =>
          (sourceTerms c).map fun t2 =>
            ((derivativeTerms t1 a).flatMap fun u =>
              (derivativeTerms t2 a).map fun v => termOverlap u v).sum).sum := by
    unfold overlapProgram termOverlapProgram
    rw [map_flatMap, flatMap_sum]
    conv_rhs => rw [flatMap_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t1 _
    simp only [map_flatMap, flatMap_sum]
    rw [list_sum_swap (derivativeTerms t1 a) (sourceTerms c)
        (fun u t2 => ((derivativeTerms t2 a).map (termOverlap u)).sum)]
  have outer :
      (∑ a : Fin 3, ((sourceTerms b).flatMap fun t1 =>
          (sourceTerms c).map fun t2 =>
            ((derivativeTerms t1 a).flatMap fun u =>
              (derivativeTerms t2 a).map fun v => termOverlap u v).sum).sum) =
        ((sourceTerms b).flatMap fun t1 => (sourceTerms c).map fun t2 =>
          ∑ a : Fin 3, ((derivativeTerms t1 a).flatMap fun u =>
            (derivativeTerms t2 a).map fun v => termOverlap u v).sum).sum := by
    calc (∑ a : Fin 3, ((sourceTerms b).flatMap fun t1 =>
            (sourceTerms c).map fun t2 =>
              ((derivativeTerms t1 a).flatMap fun u =>
                (derivativeTerms t2 a).map fun v => termOverlap u v).sum).sum)
        = ∑ a : Fin 3, ((sourceTerms b).map fun t1 =>
            ((sourceTerms c).map fun t2 =>
              ((derivativeTerms t1 a).flatMap fun u =>
                (derivativeTerms t2 a).map fun v => termOverlap u v).sum).sum).sum := by
          apply Finset.sum_congr rfl
          intro a _
          exact flatMap_sum _ _
      _ = ((sourceTerms b).map fun t1 =>
            ∑ a : Fin 3, ((sourceTerms c).map fun t2 =>
              ((derivativeTerms t1 a).flatMap fun u =>
                (derivativeTerms t2 a).map fun v => termOverlap u v).sum).sum).sum :=
          (list_map_finset_sum _ _ _).symm
      _ = ((sourceTerms b).map fun t1 =>
            ((sourceTerms c).map fun t2 =>
              ∑ a : Fin 3, ((derivativeTerms t1 a).flatMap fun u =>
                (derivativeTerms t2 a).map fun v => termOverlap u v).sum).sum).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro t1 _
          exact (list_map_finset_sum _ _ _).symm
      _ = _ := (flatMap_sum _ _).symm
  rw [show kinetic b c = (1/2 : ℝ) * ∑ a : Fin 3,
      overlapProgram ((sourceTerms b).flatMap (derivativeTerms · a))
        ((sourceTerms c).flatMap (derivativeTerms · a)) from by
    unfold kinetic
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact axis a]
  simp only [axisProgram]
  rw [outer]
  have rhs : ((kineticDescriptors b c).map descriptorValue).sum =
      ((sourceTerms b).map fun t1 =>
        ((sourceTerms c).map fun t2 =>
          (kineticCoefficient t1 t2 : ℝ) *
            radialKernel (pairExponent t1 t2) (pairPenalty t1 t2)).sum).sum := by
    unfold kineticDescriptors kineticDescriptor descriptorValue
    rw [map_flatMap, flatMap_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t1 _
    rw [List.map_map]
    rfl
  rw [rhs]
  rw [flatMap_sum, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t1 _
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t2 _
  exact kinetic_pair_descriptor t1 t2

end
end LAlanine40K2025.UnifiedOrbitals.Kinetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
