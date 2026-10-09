import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericHeat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def sourceS (i : Basis) : Prop :=
  ∀ term ∈ sourceTerms i, sPowers term

theorem pair_terms_s (i j : Basis) (hi : sourceS i) (hj : sourceS j)
    (pair : Term × Term) (member : pair ∈ pairTerms i j) :
    sPowers pair.1 ∧ sPowers pair.2 := by
  rcases List.mem_flatMap.mp member with ⟨left,leftMember,rightMember⟩
  rcases List.mem_map.mp rightMember with ⟨right,rightIn,identified⟩
  have equality : pair = (left,right) := identified.symm
  subst pair
  exact ⟨hi left leftMember,hj right rightIn⟩

def sourceSQuartet (i j k l : Basis) : ℝ :=
  ((pairTerms i j).map fun left =>
    ((pairTerms k l).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        sHeatInner left.1 left.2 right.1 right.2 t).sum).sum

theorem source_s_quartet (i j k l : Basis)
    (hi : sourceS i) (hj : sourceS j)
    (hk : sourceS k) (hl : sourceS l) :
    electronRepulsion i j k l = sourceSQuartet i j k l := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite sourceSQuartet
  apply congrArg List.sum
  apply List.map_congr_left
  intro left leftMember
  apply congrArg List.sum
  apply List.map_congr_left
  intro right rightMember
  have hsLeft := pair_terms_s i j hi hj left leftMember
  have hsRight := pair_terms_s k l hk hl right rightMember
  have hpLeft := pair_terms_positive i j left leftMember
  have hpRight := pair_terms_positive k l right rightMember
  exact s_primitive_outer left.1 left.2 right.1 right.2
    hsLeft.1 hsLeft.2 hsRight.1 hsRight.2
    hpLeft.1 hpLeft.2 hpRight.1 hpRight.2

theorem source_s_2 : sourceS 2 := by
  intro term member
  rw [original_s_singleton] at member
  have equality := List.mem_singleton.mp member
  subst term
  exact original_s_powers

theorem source_s_14_raw :
    (sourceTerms (14 : Basis)).all
      (fun term => decide (∀ axis : Fin 3, term.powers axis = 0)) = true := by
  decide +kernel

theorem source_s_14 : sourceS 14 := by
  simpa only [sourceS,sPowers,List.all_eq_true,decide_eq_true_eq]
    using source_s_14_raw

theorem original_s_cross_quartet :
    electronRepulsion 2 2 14 14 = sourceSQuartet 2 2 14 14 :=
  source_s_quartet 2 2 14 14 source_s_2 source_s_2 source_s_14 source_s_14

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
