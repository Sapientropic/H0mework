import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.J

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource SourceCoulomb MeasureTheory
noncomputable section

private theorem double_list_sum {α β : Type*} (left : List α) (right : List β)
    (f : α → ℝ) (g : β → ℝ) (scale : ℝ) :
    (left.map f).sum * (right.map g).sum * scale =
      (left.map fun a => (right.map fun b => f a * g b * scale).sum).sum := by
  have each (a : α) : f a * (right.map g).sum * scale =
      (right.map fun b => f a * g b * scale).sum := by
    induction right with
    | nil => simp
    | cons b rest ih => simp only [List.map_cons,List.sum_cons]; rw [← ih]; ring
  induction left with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [← each a,← ih]
      ring

private theorem integrable_list_sum {α : Type*} (items : List α)
    (f : α → Point × Point → ℝ)
    (each : ∀ item ∈ items, Integrable (f item)) :
    Integrable (fun z : Point × Point => (items.map fun item => f item z).sum) := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have tail : ∀ next ∈ rest, Integrable (f next) := by
        intro next member
        exact each next (by simp [member])
      change Integrable (f item + fun z : Point × Point =>
        (rest.map fun next => f next z).sum)
      exact (each item (by simp)).add (ih tail)

private theorem integral_list_sum {α : Type*} (items : List α)
    (f : α → Point × Point → ℝ)
    (each : ∀ item ∈ items, Integrable (f item)) :
    (∫ z : Point × Point, (items.map fun item => f item z).sum) =
      (items.map fun item => ∫ z : Point × Point, f item z).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have tail : ∀ next ∈ rest, Integrable (f next) := by
        intro next member
        exact each next (by simp [member])
      simp only [List.map_cons,List.sum_cons]
      rw [integral_add (each item (by simp)) (integrable_list_sum rest f tail),ih tail]

def primitiveInteraction (left right : Term × Term) : ℝ :=
  ∫ z : Point × Point,
    pairShape left.1 left.2 z.1 * pairShape right.1 right.2 z.2 *
      kernel (z.2 - z.1)

def pairInteractionFinite (i j k l : Basis) : ℝ :=
  ((pairTerms i j).map fun left =>
    ((pairTerms k l).map fun right => primitiveInteraction left right).sum).sum

theorem pair_interaction_finite (i j k l : Basis) :
    pairInteraction i j k l = pairInteractionFinite i j k l := by
  let P := pairTerms i j
  let Q := pairTerms k l
  let F : (Term × Term) → (Term × Term) → Point × Point → ℝ :=
    fun left right z =>
      pairShape left.1 left.2 z.1 * pairShape right.1 right.2 z.2 *
        kernel (z.2 - z.1)
  have each (left : Term × Term) (leftMember : left ∈ P)
      (right : Term × Term) (rightMember : right ∈ Q) :
      Integrable (F left right) := by
    have hp := pair_terms_positive i j left leftMember
    have hq := pair_terms_positive k l right rightMember
    exact pair_kernel_integrable left.1 left.2 right.1 right.2
      hp.1 hp.2 hq.1 hq.2
  have inner (left : Term × Term) (leftMember : left ∈ P) :
      Integrable (fun z : Point × Point => (Q.map fun right => F left right z).sum) :=
    integrable_list_sum Q (F left) (fun right rightMember =>
      each left leftMember right rightMember)
  have pointwise (z : Point × Point) :
      sourcePair i j z.1 * sourcePair k l z.2 * kernel (z.2 - z.1) =
        (P.map fun left => (Q.map fun right => F left right z).sum).sum := by
    rw [source_pair_flat i j z.1,source_pair_flat k l z.2]
    exact double_list_sum P Q
      (fun left => pairShape left.1 left.2 z.1)
      (fun right => pairShape right.1 right.2 z.2)
      (kernel (z.2 - z.1))
  have innerIntegral (left : Term × Term) (leftMember : left ∈ P) :
      (∫ z : Point × Point, (Q.map fun right => F left right z).sum) =
        (Q.map fun right => ∫ z : Point × Point, F left right z).sum :=
    integral_list_sum Q (F left) (fun right rightMember =>
      each left leftMember right rightMember)
  unfold pairInteraction pairInteractionFinite
  calc
    (∫ z : Point × Point,
      sourcePair i j z.1 * sourcePair k l z.2 * kernel (z.2 - z.1)) =
        ∫ z : Point × Point,
          (P.map fun left => (Q.map fun right => F left right z).sum).sum := by
      congr 1
      funext z
      exact pointwise z
    _ = (P.map fun left => ∫ z : Point × Point,
          (Q.map fun right => F left right z).sum).sum :=
      integral_list_sum P (fun left z => (Q.map fun right => F left right z).sum) inner
    _ = (P.map fun left => (Q.map fun right =>
          ∫ z : Point × Point, F left right z).sum).sum := by
      congr 1
      apply List.map_congr_left
      intro left leftMember
      exact innerIntegral left leftMember
    _ = _ := rfl

theorem sourceJ_primitive_finite (i j : Basis) :
    AO.sourceJ i j =
      ∑ k : Basis, ∑ l : Basis,
        Proxy.Correction.d3AO k l * pairInteractionFinite k l i j := by
  rw [sourceJ_pair_normal_form]
  simp only [pair_interaction_finite]

theorem original_hartree_primitive_finite :
    Interaction.d3HartreeEnergy = (1 / 2 : ℝ) *
      ∑ i : Basis, ∑ j : Basis,
        Proxy.Correction.d3AO i j *
          (∑ k : Basis, ∑ l : Basis,
            Proxy.Correction.d3AO k l * pairInteractionFinite k l i j) := by
  rw [original_hartree_pair_normal_form]
  simp only [pair_interaction_finite]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
