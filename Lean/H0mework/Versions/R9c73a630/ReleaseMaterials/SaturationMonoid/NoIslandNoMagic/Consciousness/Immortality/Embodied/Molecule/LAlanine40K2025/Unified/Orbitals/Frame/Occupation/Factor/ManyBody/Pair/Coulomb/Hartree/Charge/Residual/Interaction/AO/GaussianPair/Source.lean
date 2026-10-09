import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Primitive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
noncomputable section

def sourcePair (i j : Basis) (x : Point) : ℝ :=
  ((sourceTerms i).map fun left =>
    ((sourceTerms j).map fun right => pairShape left right x).sum).sum

def pairTerms (i j : Basis) : List (Term × Term) :=
  (sourceTerms i).flatMap fun left =>
    (sourceTerms j).map fun right => (left,right)

private theorem nested_sum_flat (left right : List Term) (f : Term → Term → ℝ) :
    ((left.map fun a => (right.map fun b => f a b).sum).sum) =
      ((left.flatMap fun a => right.map fun b => (a,b)).map
        fun pair => f pair.1 pair.2).sum := by
  induction left with
  | nil => simp
  | cons term rest ih => simp [ih,List.map_append,List.sum_append,Function.comp_def]

theorem source_pair_flat (i j : Basis) (x : Point) :
    sourcePair i j x =
      ((pairTerms i j).map fun pair => pairShape pair.1 pair.2 x).sum :=
  nested_sum_flat (sourceTerms i) (sourceTerms j) (fun a b => pairShape a b x)

theorem pair_terms_positive (i j : Basis) (pair : Term × Term)
    (member : pair ∈ pairTerms i j) :
    0 < pair.1.exponent ∧ 0 < pair.2.exponent := by
  rcases List.mem_flatMap.mp member with ⟨left,leftMember,rightMember⟩
  rcases List.mem_map.mp rightMember with ⟨right,rightIn,identified⟩
  have equality : pair = (left,right) := identified.symm
  subst pair
  exact ⟨source_exponents_positive i left leftMember,
    source_exponents_positive j right rightIn⟩

private theorem term_orbital_pair (left : Term) (right : List Term) (x : Point)
    (leftPositive : 0 < left.exponent)
    (rightPositive : ∀ term ∈ right, 0 < term.exponent) :
    value left (fun _ => 0) x * SourceGaussianModel.orbital right (fun _ => 0) x =
      (right.map fun term => pairShape left term x).sum := by
  induction right with
  | nil => simp [SourceGaussianModel.orbital]
  | cons term rest ih =>
      have termPositive : 0 < term.exponent := rightPositive term (by simp)
      have restPositive : ∀ other ∈ rest, 0 < other.exponent := by
        intro other membership
        exact rightPositive other (by simp [membership])
      have sumPositive : (left.exponent : ℝ) + (term.exponent : ℝ) ≠ 0 := by
        apply ne_of_gt
        exact add_pos (by exact_mod_cast leftPositive) (by exact_mod_cast termPositive)
      simp only [SourceGaussianModel.orbital] at ih
      simp only [SourceGaussianModel.orbital,List.map_cons,List.sum_cons,mul_add]
      rw [value_pair left term x sumPositive,ih restPositive]

private theorem orbital_pair_expand (left right : List Term) (x : Point)
    (leftPositive : ∀ term ∈ left, 0 < term.exponent)
    (rightPositive : ∀ term ∈ right, 0 < term.exponent) :
    SourceGaussianModel.orbital left (fun _ => 0) x *
      SourceGaussianModel.orbital right (fun _ => 0) x =
      (left.map fun term => (right.map fun other => pairShape term other x).sum).sum := by
  induction left with
  | nil => simp [SourceGaussianModel.orbital]
  | cons term rest ih =>
      have termPositive : 0 < term.exponent := leftPositive term (by simp)
      have restPositive : ∀ other ∈ rest, 0 < other.exponent := by
        intro other membership
        exact leftPositive other (by simp [membership])
      have hterm := term_orbital_pair term right x termPositive rightPositive
      simp only [SourceGaussianModel.orbital] at hterm
      simp only [SourceGaussianModel.orbital] at ih
      simp only [SourceGaussianModel.orbital,List.map_cons,List.sum_cons,add_mul]
      rw [hterm,ih restPositive]

theorem source_pair_exact (i j : Basis) (x : Point) :
    ao i x * ao j x = sourcePair i j x := by
  exact orbital_pair_expand (sourceTerms i) (sourceTerms j) x
    (source_exponents_positive i) (source_exponents_positive j)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
