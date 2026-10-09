import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Heat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem general_primitive_outer (left right nextLeft nextRight : Term)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (left,right) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ), pairHeatInner left right nextLeft nextRight t := by
  unfold Laplace.primitiveHeatInteraction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact pair_heat_inner_closed left right nextLeft nextRight t
    hleftDegree hrightDegree hleftPos hrightPos
    hnextLeft hnextRight hnextLeftPos hnextRightPos ht

def sourceHighQuartet (sourceLeft sourceRight i j : Basis) : ℝ :=
  ((pairTerms sourceLeft sourceRight).map fun left =>
    ((pairTerms i j).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        pairHeatInner left.1 left.2 right.1 right.2 t).sum).sum

theorem source_high_quartet (sourceLeft sourceRight i j : Basis)
    (hi : Axis.sourceS i) (hj : Axis.sourceS j) :
    electronRepulsion sourceLeft sourceRight i j =
      sourceHighQuartet sourceLeft sourceRight i j := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite sourceHighQuartet
  apply congrArg List.sum
  apply List.map_congr_left
  intro left leftMember
  apply congrArg List.sum
  apply List.map_congr_left
  intro right rightMember
  rcases List.mem_flatMap.mp leftMember with ⟨sourceTerm,sourceTermIn,leftRest⟩
  rcases List.mem_map.mp leftRest with ⟨sourceOther,sourceOtherIn,identified⟩
  have hleft : left = (sourceTerm,sourceOther) := identified.symm
  subst left
  have hnext := Axis.pair_terms_s i j hi hj right rightMember
  have hpos := pair_terms_positive sourceLeft sourceRight
    (sourceTerm,sourceOther) leftMember
  have hnextPos := pair_terms_positive i j right rightMember
  exact general_primitive_outer sourceTerm sourceOther right.1 right.2
    (Shift.all_original_low_degree sourceLeft sourceTerm sourceTermIn)
    (Shift.all_original_low_degree sourceRight sourceOther sourceOtherIn)
    hpos.1 hpos.2 hnext.1 hnext.2 hnextPos.1 hnextPos.2

theorem source_high_s_targets_quartet (sourceLeft sourceRight i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    electronRepulsion sourceLeft sourceRight i j =
      sourceHighQuartet sourceLeft sourceRight i j :=
  source_high_quartet sourceLeft sourceRight i j
    (Axis.source_s_bases_sound i hi)
    (Axis.source_s_bases_sound j hj)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
