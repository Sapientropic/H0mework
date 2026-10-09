import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Integrability
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def sourceCompactQuartet
    (sourceLeft sourceRight targetLeft targetRight : Basis) : ℝ :=
  ((pairTerms sourceLeft sourceRight).map fun left =>
    ((pairTerms targetLeft targetRight).map fun right =>
      compactifiedPrimitive left.1 left.2 right.1 right.2).sum).sum

theorem source_compact_quartet
    (sourceLeft sourceRight targetLeft targetRight : Basis) :
    electronRepulsion sourceLeft sourceRight targetLeft targetRight =
      sourceCompactQuartet sourceLeft sourceRight targetLeft targetRight := by
  rw [TargetFull.source_full_quartet]
  unfold TargetFull.sourceFullQuartet sourceCompactQuartet
  apply congrArg List.sum
  apply List.map_congr_left
  intro left _
  apply congrArg List.sum
  apply List.map_congr_left
  intro right _
  exact compactify_integral
    (TargetFull.targetFullHeatInner left.1 left.2 right.1 right.2)

theorem source_compact_terms_integrable
    (sourceLeft sourceRight targetLeft targetRight : Basis)
    (left : Term × Term) (hleft : left ∈ pairTerms sourceLeft sourceRight)
    (right : Term × Term) (hright : right ∈ pairTerms targetLeft targetRight) :
    IntegrableOn
      (compactifiedHeatInner left.1 left.2 right.1 right.2)
      (Ioo (0 : ℝ) 1) := by
  rcases List.mem_flatMap.mp hleft with ⟨sourceTerm,sourceTermIn,leftRest⟩
  rcases List.mem_map.mp leftRest with ⟨sourceOther,sourceOtherIn,identifiedLeft⟩
  have hl : left = (sourceTerm,sourceOther) := identifiedLeft.symm
  subst left
  rcases List.mem_flatMap.mp hright with ⟨targetTerm,targetTermIn,rightRest⟩
  rcases List.mem_map.mp rightRest with ⟨targetOther,targetOtherIn,identifiedRight⟩
  have hr : right = (targetTerm,targetOther) := identifiedRight.symm
  subst right
  have hsourcePos := pair_terms_positive sourceLeft sourceRight
    (sourceTerm,sourceOther) hleft
  have htargetPos := pair_terms_positive targetLeft targetRight
    (targetTerm,targetOther) hright
  exact compactified_outer_integrable sourceTerm sourceOther targetTerm targetOther
    (Shift.all_original_low_degree sourceLeft sourceTerm sourceTermIn)
    (Shift.all_original_low_degree sourceRight sourceOther sourceOtherIn)
    (Shift.all_original_low_degree targetLeft targetTerm targetTermIn)
    (Shift.all_original_low_degree targetRight targetOther targetOtherIn)
    hsourcePos.1 hsourcePos.2 htargetPos.1 htargetPos.2

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
