import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : TargetFull.Material
  integrationInterval : Set ℝ
  analyticQuartet : Basis → Basis → Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := TargetFull.material
  integrationInterval := Set.Ioo 0 1
  analyticQuartet := sourceCompactQuartet
  combinedTargetJ := targetCompactJ

theorem parent_identity : material.parent = TargetFull.material := rfl
theorem interval_identity : material.integrationInterval = Set.Ioo (0 : ℝ) 1 := rfl

theorem quartet_exact (sourceLeft sourceRight targetLeft targetRight : Basis) :
    electronRepulsion sourceLeft sourceRight targetLeft targetRight =
      material.analyticQuartet sourceLeft sourceRight targetLeft targetRight :=
  source_compact_quartet sourceLeft sourceRight targetLeft targetRight

theorem target_J_all (i j : Basis) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j := by
  simpa only [material] using target_compact_J i j

theorem installed_parent_same_source (i j : Basis) :
    material.parent.combinedTargetJ i j = material.combinedTargetJ i j := by
  simpa only [material, TargetFull.material] using
    parent_same_source i j

structure Closure : Prop where
  parent : TargetFull.Closure
  compactification : type_of% compactify_integral
  primitive : type_of% primitive_outer_compactified
  integrability : type_of% source_compact_terms_integrable
  sourceQuartet : type_of% source_compact_quartet
  targetAll : type_of% target_compact_J
  parentIdentity : type_of% parent_identity
  intervalIdentity : type_of% interval_identity
  installedQuartet : type_of% quartet_exact
  installedJ : type_of% target_J_all
  sameSource : type_of% installed_parent_same_source

theorem sourceGeneratedClosure : Closure :=
  ⟨TargetFull.sourceGeneratedClosure,compactify_integral,
    primitive_outer_compactified,source_compact_terms_integrable,
    source_compact_quartet,target_compact_J,
    parent_identity,interval_identity,quartet_exact,target_J_all,
    installed_parent_same_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
