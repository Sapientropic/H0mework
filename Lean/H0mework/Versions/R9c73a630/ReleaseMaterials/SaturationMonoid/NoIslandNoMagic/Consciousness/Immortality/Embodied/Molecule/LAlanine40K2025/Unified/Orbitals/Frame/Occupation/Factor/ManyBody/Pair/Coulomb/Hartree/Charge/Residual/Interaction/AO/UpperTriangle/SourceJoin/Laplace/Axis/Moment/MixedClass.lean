import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedQuartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceClass

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

def sourceP0SQuartet (i j : Basis) : ℝ :=
  ((pairTerms (3 : Basis) 2).map fun left =>
    ((pairTerms i j).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        p0SHeatInner left.1 right.1 right.2 t).sum).sum

theorem source_p0_s_quartet (i j : Basis)
    (hi : Axis.sourceS i) (hj : Axis.sourceS j) :
    electronRepulsion 3 2 i j = sourceP0SQuartet i j := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite sourceP0SQuartet
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
  exact p0_s_primitive_outer term right.1 right.2
    (original_p0_source term termMember)
    (source_exponents_positive 3 term termMember)
    hs.1 hs.2 hpos.1 hpos.2

theorem source_p0_s_bases_quartet (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    electronRepulsion 3 2 i j = sourceP0SQuartet i j :=
  source_p0_s_quartet i j
    (Axis.source_s_bases_sound i hi)
    (Axis.source_s_bases_sound j hj)

theorem old_cross_is_class_instance :
    originalP0SCrossQuartet = sourceP0SQuartet 14 14 := rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
