import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedClassTarget
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Family
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : Mixed.Material
  sBases : Finset Basis
  analyticQuartet : Basis → Basis → ℝ
  targetRest : Basis → Basis → ℝ

def material : Material where
  parent := Mixed.material
  sBases := Axis.sourceSBases
  analyticQuartet := Moment.sourceP0SQuartet
  targetRest := Moment.targetP0SRest

theorem parent_identity : material.parent = Mixed.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card

theorem quartet_exact (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    electronRepulsion 3 2 i j = material.analyticQuartet i j :=
  Moment.source_p0_s_bases_quartet i j hi hj

theorem target_J_s_class (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    SourceJoin.material.targetJ i j =
      (SourceJoin.sourceCoefficientAt (196 : Fin 4851) : ℝ) *
        material.analyticQuartet i j + material.targetRest i j :=
  Moment.target_p0_s_J i j hi hj

structure Closure : Prop where
  parent : Mixed.Closure
  sourceClass : type_of% Moment.source_p0_s_bases_quartet
  targetClass : type_of% Moment.target_p0_s_J
  crossInstance : type_of% Moment.old_cross_is_class_instance
  targetInstance : type_of% Moment.old_cross_target_is_class_instance
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_s_class

theorem sourceGeneratedClosure : Closure :=
  ⟨Mixed.sourceGeneratedClosure,Moment.source_p0_s_bases_quartet,
    Moment.target_p0_s_J,Moment.old_cross_is_class_instance,
    Moment.old_cross_target_is_class_instance,parent_identity,
    s_basis_count,quartet_exact,target_J_s_class⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
