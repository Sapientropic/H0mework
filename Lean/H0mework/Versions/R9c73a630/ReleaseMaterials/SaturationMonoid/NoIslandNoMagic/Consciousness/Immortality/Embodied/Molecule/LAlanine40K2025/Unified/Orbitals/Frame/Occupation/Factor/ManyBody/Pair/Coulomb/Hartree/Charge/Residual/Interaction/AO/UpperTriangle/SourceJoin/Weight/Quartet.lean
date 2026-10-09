import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Primitive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Finite

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceFiniteData SourceExponential SourceCoulomb GlobalSource
open GaussianPair Laplace.Axis
open MeasureTheory Set
noncomputable section

theorem actual_source_exponents_ge :
    ∀ j : Basis, (sourceTerms j).all
      (fun term => decide ((1/64 : ℚ) ≤ term.exponent)) = true := by
  decide +kernel

theorem source_exponents_ge (j : Basis) :
    ∀ term ∈ sourceTerms j, (1/64 : ℚ) ≤ term.exponent := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using
    actual_source_exponents_ge j

theorem pair_terms_exponents_ge (i j : Basis) (pair : Term × Term)
    (member : pair ∈ pairTerms i j) :
    (1/64 : ℚ) ≤ pair.1.exponent ∧ (1/64 : ℚ) ≤ pair.2.exponent := by
  rcases List.mem_flatMap.mp member with ⟨left,leftMember,rightMember⟩
  rcases List.mem_map.mp rightMember with ⟨right,rightIn,identified⟩
  have equality : pair = (left,right) := identified.symm
  subst pair
  exact ⟨source_exponents_ge i left leftMember,
    source_exponents_ge j right rightIn⟩

theorem primitive_abs_le_pairTau_of_mem (i j k l : Basis)
    (left right : Term × Term)
    (leftMember : left ∈ pairTerms i j)
    (rightMember : right ∈ pairTerms k l) :
    |GaussianPair.primitiveInteraction left right| ≤
      (pairTau left.1 left.2 : ℝ) * (pairTau right.1 right.2 : ℝ) := by
  obtain ⟨h1,h2⟩ := pair_terms_positive i j left leftMember
  obtain ⟨h3,h4⟩ := pair_terms_positive k l right rightMember
  obtain ⟨g1,g2⟩ := pair_terms_exponents_ge i j left leftMember
  obtain ⟨g3,g4⟩ := pair_terms_exponents_ge k l right rightMember
  exact primitiveInteraction_abs_le _ _ _ _ h1 h2 h3 h4
    (pairRateM_ge _ _ g1 g2) (pairRateM_ge _ _ g3 g4)

def pairMajorant (k l : Basis) : ℚ :=
  ((pairTerms k l).map fun q => pairTau q.1 q.2).sum

theorem pairMajorant_nonneg (k l : Basis) : 0 ≤ pairMajorant k l := by
  unfold pairMajorant
  apply List.sum_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨q,qmem,qeq⟩
  rw [← qeq]
  exact pairTau_nonneg _ _
    (pair_terms_positive _ _ q qmem).1.le
    (pair_terms_positive _ _ q qmem).2.le
    (pairRateM_pos _ _
      (pair_terms_positive _ _ q qmem).1
      (pair_terms_positive _ _ q qmem).2)
    (pairPhi_pos _ _
      (pairRateM_ge _ _
        (pair_terms_exponents_ge _ _ q qmem).1
        (pair_terms_exponents_ge _ _ q qmem).2))

private theorem list_abs_sum_le {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map fun x => |f x|).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)

private theorem rat_list_sum_cast (l : List ℚ) :
    ((l.sum : ℚ) : ℝ) = (l.map (Rat.cast : ℚ → ℝ)).sum := by
  have h := map_list_sum (Rat.castHom ℝ) l
  simp only [Rat.coe_castHom] at h
  exact h

theorem electron_repulsion_majorant (k l i j : Basis) :
    |electronRepulsion k l i j| ≤
      (pairMajorant k l : ℝ) * (pairMajorant i j : ℝ) := by
  rw [← pair_interaction_source k l i j, pair_interaction_finite]
  unfold pairInteractionFinite pairMajorant
  rw [rat_list_sum_cast, rat_list_sum_cast]
  calc |((pairTerms k l).map fun left =>
          ((pairTerms i j).map fun right =>
            GaussianPair.primitiveInteraction left right).sum).sum|
      ≤ ((pairTerms k l).map fun left =>
          |((pairTerms i j).map fun right =>
            GaussianPair.primitiveInteraction left right).sum|).sum :=
        list_abs_sum_le _ _
    _ ≤ ((pairTerms k l).map fun left =>
          (pairTau left.1 left.2 : ℝ) * ((pairTerms i j).map
            fun q => (pairTau q.1 q.2 : ℝ)).sum).sum :=
        List.sum_le_sum (fun left leftMember =>
          (list_abs_sum_le _ _).trans
            ((List.sum_le_sum (fun right rightMember =>
              primitive_abs_le_pairTau_of_mem k l i j left right
                leftMember rightMember)).trans
              (le_of_eq (List.sum_map_mul_left _ _ _))))
    _ = ((pairTerms k l).map fun q => (pairTau q.1 q.2 : ℝ)).sum *
        ((pairTerms i j).map fun q => (pairTau q.1 q.2 : ℝ)).sum := by
        rw [← List.sum_map_mul_right]
    _ = (((pairTerms k l).map fun q => pairTau q.1 q.2).map
            (Rat.cast : ℚ → ℝ)).sum *
        (((pairTerms i j).map fun q => pairTau q.1 q.2).map
            (Rat.cast : ℚ → ℝ)).sum := by
        rw [List.map_map, List.map_map]
        congr 1

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
