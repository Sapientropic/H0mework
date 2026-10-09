import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.Heat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem p_axis_s_primitive_outer (axis : Fin 3) (term nextLeft nextRight : Term)
    (hp : sourcePAxis axis term) (positive : 0 < term.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (term,Axis.originalS) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ), pAxisSHeatInner axis term nextLeft nextRight t := by
  unfold Laplace.primitiveHeatInteraction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact p_axis_s_heat_inner_closed axis term nextLeft nextRight t
    hp positive hnextLeft hnextRight hnextLeftPos hnextRightPos ht

def sourcePAxisSQuartet (axis : Fin 3) (i j : Basis) : ℝ :=
  ((pairTerms (pBasis axis) 2).map fun left =>
    ((pairTerms i j).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        pAxisSHeatInner axis left.1 right.1 right.2 t).sum).sum

theorem source_p_axis_s_quartet (axis : Fin 3) (i j : Basis)
    (hi : Axis.sourceS i) (hj : Axis.sourceS j) :
    electronRepulsion (pBasis axis) 2 i j = sourcePAxisSQuartet axis i j := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite sourcePAxisSQuartet
  apply congrArg List.sum
  apply List.map_congr_left
  intro left leftMember
  apply congrArg List.sum
  apply List.map_congr_left
  intro right rightMember
  rcases List.mem_flatMap.mp leftMember with ⟨term,termMember,leftRest⟩
  rcases List.mem_map.mp leftRest with ⟨firstRight,firstRightIn,identified⟩
  rw [Axis.original_s_singleton] at firstRightIn
  have hfirstRight : firstRight = Axis.originalS := List.mem_singleton.mp firstRightIn
  subst firstRight
  have hleft : left = (term,Axis.originalS) := identified.symm
  subst left
  have hs := Axis.pair_terms_s i j hi hj right rightMember
  have hpos := pair_terms_positive i j right rightMember
  exact p_axis_s_primitive_outer axis term right.1 right.2
    (original_p_axes_source axis term termMember)
    (source_exponents_positive (pBasis axis) term termMember)
    hs.1 hs.2 hpos.1 hpos.2

theorem source_p_axis_s_bases_quartet (axis : Fin 3) (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    electronRepulsion (pBasis axis) 2 i j = sourcePAxisSQuartet axis i j :=
  source_p_axis_s_quartet axis i j
    (Axis.source_s_bases_sound i hi)
    (Axis.source_s_bases_sound j hj)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
