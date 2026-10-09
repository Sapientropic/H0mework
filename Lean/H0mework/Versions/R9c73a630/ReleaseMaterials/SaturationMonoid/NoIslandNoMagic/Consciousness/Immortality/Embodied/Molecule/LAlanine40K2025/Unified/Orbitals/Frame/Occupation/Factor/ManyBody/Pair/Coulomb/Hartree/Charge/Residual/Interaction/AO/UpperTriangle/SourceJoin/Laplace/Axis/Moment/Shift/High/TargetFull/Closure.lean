import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : TargetLinear.Material
  analyticTargets : Finset (Basis × Basis)
  analyticQuartet : Basis → Basis → Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := TargetLinear.material
  analyticTargets := allTargetEntries
  analyticQuartet := sourceFullQuartet
  combinedTargetJ := targetFullJ

theorem parent_identity : material.parent = TargetLinear.material := rfl
theorem target_count : material.analyticTargets.card = 9604 := all_target_entries_card

theorem quartet_exact (sourceLeft sourceRight targetLeft targetRight : Basis) :
    electronRepulsion sourceLeft sourceRight targetLeft targetRight =
      material.analyticQuartet sourceLeft sourceRight targetLeft targetRight :=
  source_full_quartet sourceLeft sourceRight targetLeft targetRight

theorem target_J_all (i j : Basis) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j := by
  simpa only [material] using target_full_J i j

theorem parent_same_source (i j : Basis) :
    material.parent.combinedTargetJ i j = material.combinedTargetJ i j := by
  simpa only [material, TargetLinear.material] using
    prior_linear_same_source i j

structure Closure : Prop where
  parent : TargetLinear.Closure
  gaussianRecurrence : type_of% iterated_deriv_g
  eighthMoment : type_of% gaussian_moment_eight
  rawMoments : type_of% raw_moment_eight
  fourPolynomial : type_of% four_poly_integral
  coupledAxis : type_of% target_full_axis_integral
  spatial : type_of% spatial_target_full_factor
  sourceQuartet : type_of% source_full_quartet
  targetCount : type_of% all_target_entries_card
  targetAll : type_of% target_full_J
  parentIdentity : type_of% parent_identity
  installedTargetCount : type_of% target_count
  installedQuartet : type_of% quartet_exact
  installedJ : type_of% target_J_all
  sameSource : type_of% parent_same_source

theorem sourceGeneratedClosure : Closure :=
  ⟨TargetLinear.sourceGeneratedClosure,iterated_deriv_g,
    gaussian_moment_eight,raw_moment_eight,four_poly_integral,
    target_full_axis_integral,spatial_target_full_factor,
    source_full_quartet,all_target_entries_card,target_full_J,
    parent_identity,target_count,quartet_exact,target_J_all,
    parent_same_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
