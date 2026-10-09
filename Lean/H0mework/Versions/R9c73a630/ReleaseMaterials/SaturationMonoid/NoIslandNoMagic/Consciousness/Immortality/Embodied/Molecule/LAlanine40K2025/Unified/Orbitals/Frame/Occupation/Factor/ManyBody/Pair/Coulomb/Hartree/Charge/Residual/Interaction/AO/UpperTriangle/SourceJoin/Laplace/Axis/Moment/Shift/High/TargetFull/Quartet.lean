import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Heat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem target_full_primitive_outer
    (left right nextLeft nextRight : Term)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hnextLeftDegree : Shift.sourceLowDegree nextLeft)
    (hnextRightDegree : Shift.sourceLowDegree nextRight)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (left,right) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ), targetFullHeatInner left right nextLeft nextRight t := by
  unfold Laplace.primitiveHeatInteraction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact target_full_heat_inner_closed left right nextLeft nextRight t
    hleftDegree hrightDegree hnextLeftDegree hnextRightDegree
    hleftPos hrightPos hnextLeftPos hnextRightPos ht

def sourceFullQuartet (sourceLeft sourceRight targetLeft targetRight : Basis) : ℝ :=
  ((pairTerms sourceLeft sourceRight).map fun left =>
    ((pairTerms targetLeft targetRight).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        targetFullHeatInner left.1 left.2 right.1 right.2 t).sum).sum

theorem source_full_quartet
    (sourceLeft sourceRight targetLeft targetRight : Basis) :
    electronRepulsion sourceLeft sourceRight targetLeft targetRight =
      sourceFullQuartet sourceLeft sourceRight targetLeft targetRight := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite sourceFullQuartet
  apply congrArg List.sum
  apply List.map_congr_left
  intro left leftMember
  apply congrArg List.sum
  apply List.map_congr_left
  intro right rightMember
  rcases List.mem_flatMap.mp leftMember with ⟨sourceTerm,sourceTermIn,leftRest⟩
  rcases List.mem_map.mp leftRest with ⟨sourceOther,sourceOtherIn,identifiedLeft⟩
  have hleft : left = (sourceTerm,sourceOther) := identifiedLeft.symm
  subst left
  rcases List.mem_flatMap.mp rightMember with ⟨targetTerm,targetTermIn,rightRest⟩
  rcases List.mem_map.mp rightRest with ⟨targetOther,targetOtherIn,identifiedRight⟩
  have hright : right = (targetTerm,targetOther) := identifiedRight.symm
  subst right
  have hpos := pair_terms_positive sourceLeft sourceRight
    (sourceTerm,sourceOther) leftMember
  have hnextPos := pair_terms_positive targetLeft targetRight
    (targetTerm,targetOther) rightMember
  exact target_full_primitive_outer sourceTerm sourceOther targetTerm targetOther
    (Shift.all_original_low_degree sourceLeft sourceTerm sourceTermIn)
    (Shift.all_original_low_degree sourceRight sourceOther sourceOtherIn)
    (Shift.all_original_low_degree targetLeft targetTerm targetTermIn)
    (Shift.all_original_low_degree targetRight targetOther targetOtherIn)
    hpos.1 hpos.2 hnextPos.1 hnextPos.2

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
