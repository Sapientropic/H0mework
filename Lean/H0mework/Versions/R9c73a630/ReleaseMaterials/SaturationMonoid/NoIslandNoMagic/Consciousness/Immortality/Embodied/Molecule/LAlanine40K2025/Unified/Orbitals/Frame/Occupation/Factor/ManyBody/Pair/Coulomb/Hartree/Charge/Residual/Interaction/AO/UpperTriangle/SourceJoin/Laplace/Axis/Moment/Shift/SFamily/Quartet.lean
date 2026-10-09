import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily.Heat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem s_right_primitive_outer (left right nextLeft nextRight : Term)
    (hdegree : Shift.sourceLowDegree left)
    (hsourceRight : Axis.sPowers right)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (left,right) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ), sRightHeatInner left right nextLeft nextRight t := by
  unfold Laplace.primitiveHeatInteraction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact s_right_heat_inner_closed left right nextLeft nextRight t
    hdegree hsourceRight hleftPos hrightPos
    hnextLeft hnextRight hnextLeftPos hnextRightPos ht

def sourceSRightQuartet (basis sBasis i j : Basis) : ℝ :=
  ((pairTerms basis sBasis).map fun left =>
    ((pairTerms i j).map fun right =>
      ∫ t in Ioi (0 : ℝ),
        sRightHeatInner left.1 left.2 right.1 right.2 t).sum).sum

theorem source_s_right_quartet (basis sBasis i j : Basis)
    (hs : Axis.sourceS sBasis) (hi : Axis.sourceS i) (hj : Axis.sourceS j) :
    electronRepulsion basis sBasis i j = sourceSRightQuartet basis sBasis i j := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite sourceSRightQuartet
  apply congrArg List.sum
  apply List.map_congr_left
  intro left leftMember
  apply congrArg List.sum
  apply List.map_congr_left
  intro right rightMember
  rcases List.mem_flatMap.mp leftMember with ⟨term,termMember,leftRest⟩
  rcases List.mem_map.mp leftRest with ⟨firstRight,firstRightIn,identified⟩
  have hleft : left = (term,firstRight) := identified.symm
  subst left
  have hnext := Axis.pair_terms_s i j hi hj right rightMember
  have hpos := pair_terms_positive i j right rightMember
  exact s_right_primitive_outer term firstRight right.1 right.2
    (Shift.all_original_low_degree basis term termMember)
    (hs firstRight firstRightIn)
    (source_exponents_positive basis term termMember)
    (source_exponents_positive sBasis firstRight firstRightIn)
    hnext.1 hnext.2 hpos.1 hpos.2

theorem source_s_right_bases_quartet (basis sBasis i j : Basis)
    (hs : sBasis ∈ Axis.sourceSBases)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    electronRepulsion basis sBasis i j = sourceSRightQuartet basis sBasis i j :=
  source_s_right_quartet basis sBasis i j
    (Axis.source_s_bases_sound sBasis hs)
    (Axis.source_s_bases_sound i hi)
    (Axis.source_s_bases_sound j hj)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
