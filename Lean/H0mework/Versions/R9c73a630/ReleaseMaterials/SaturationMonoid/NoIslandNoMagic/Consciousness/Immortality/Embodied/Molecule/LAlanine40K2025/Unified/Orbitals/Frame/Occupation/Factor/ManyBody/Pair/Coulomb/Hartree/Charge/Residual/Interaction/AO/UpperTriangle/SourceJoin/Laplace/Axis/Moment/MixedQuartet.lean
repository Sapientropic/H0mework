import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedHeat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem p0_s_primitive_outer (term nextLeft nextRight : Term)
    (hp : sourceP0 term) (positive : 0 < term.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (term,Axis.originalS) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ), p0SHeatInner term nextLeft nextRight t := by
  unfold Laplace.primitiveHeatInteraction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact p0_s_heat_inner_closed term nextLeft nextRight t
    hp positive hnextLeft hnextRight hnextLeftPos hnextRightPos ht

def originalP0SCrossQuartet : ℝ :=
  ((pairTerms (3 : Basis) 2).map fun left =>
    ((pairTerms (14 : Basis) 14).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        p0SHeatInner left.1 right.1 right.2 t).sum).sum

theorem original_p0_s_cross_quartet :
    electronRepulsion (3 : Basis) 2 14 14 = originalP0SCrossQuartet := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite originalP0SCrossQuartet
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
  have hs := Axis.pair_terms_s 14 14 Axis.source_s_14 Axis.source_s_14
    right rightMember
  have hpos := pair_terms_positive 14 14 right rightMember
  exact p0_s_primitive_outer term right.1 right.2
    (original_p0_source term termMember)
    (source_exponents_positive 3 term termMember)
    hs.1 hs.2 hpos.1 hpos.2

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
