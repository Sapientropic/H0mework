import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Heat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem target_linear_primitive_outer
    (left right nextLeft nextRight : Term)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hnextLinear : targetLinearPowers nextLeft)
    (hnextRight : Axis.sPowers nextRight)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (left,right) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ), targetLinearHeatInner left right nextLeft nextRight t := by
  unfold Laplace.primitiveHeatInteraction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact target_linear_heat_inner_closed left right nextLeft nextRight t
    hleftDegree hrightDegree hnextLinear hnextRight
    hleftPos hrightPos hnextLeftPos hnextRightPos ht

def sourceTargetLinearQuartet
    (sourceLeft sourceRight targetLinear targetS : Basis) : ℝ :=
  ((pairTerms sourceLeft sourceRight).map fun left =>
    ((pairTerms targetLinear targetS).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        targetLinearHeatInner left.1 left.2 right.1 right.2 t).sum).sum

theorem source_target_linear_quartet
    (sourceLeft sourceRight targetLinear targetS : Basis)
    (hlinear : targetLinear ∈ targetLinearBases)
    (hs : targetS ∈ Axis.sourceSBases) :
    electronRepulsion sourceLeft sourceRight targetLinear targetS =
      sourceTargetLinearQuartet sourceLeft sourceRight targetLinear targetS := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite sourceTargetLinearQuartet
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
  have hnextPos := pair_terms_positive targetLinear targetS
    (targetTerm,targetOther) rightMember
  have htargetS := Axis.source_s_bases_sound targetS hs
  exact target_linear_primitive_outer sourceTerm sourceOther targetTerm targetOther
    (Shift.all_original_low_degree sourceLeft sourceTerm sourceTermIn)
    (Shift.all_original_low_degree sourceRight sourceOther sourceOtherIn)
    (original_target_linear_sound targetLinear hlinear targetTerm targetTermIn)
    (htargetS targetOther targetOtherIn)
    hpos.1 hpos.2 hnextPos.1 hnextPos.2

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
