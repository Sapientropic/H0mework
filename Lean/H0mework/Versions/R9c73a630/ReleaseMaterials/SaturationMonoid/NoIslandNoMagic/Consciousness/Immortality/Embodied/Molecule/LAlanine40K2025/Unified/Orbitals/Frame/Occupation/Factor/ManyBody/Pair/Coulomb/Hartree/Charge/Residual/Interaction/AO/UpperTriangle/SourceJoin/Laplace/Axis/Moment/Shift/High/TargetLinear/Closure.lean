import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Census
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : High.Material
  linearBases : Finset Basis
  sBases : Finset Basis
  analyticTargets : Finset (Basis × Basis)
  analyticQuartet : Basis → Basis → Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := High.material
  linearBases := targetLinearBases
  sBases := Axis.sourceSBases
  analyticTargets := targetLinearEntries
  analyticQuartet := sourceTargetLinearQuartet
  combinedTargetJ := targetLinearJ

theorem parent_identity : material.parent = High.material := rfl
theorem linear_basis_count : material.linearBases.card = 86 :=
  original_target_linear_card
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem analytic_target_count : material.analyticTargets.card = 4480 :=
  target_linear_entries_card

theorem quartet_exact (sourceLeft sourceRight targetLinear targetS : Basis)
    (hlinear : targetLinear ∈ material.linearBases)
    (hs : targetS ∈ material.sBases) :
    electronRepulsion sourceLeft sourceRight targetLinear targetS =
      material.analyticQuartet sourceLeft sourceRight targetLinear targetS :=
  source_target_linear_quartet sourceLeft sourceRight targetLinear targetS
    hlinear hs

theorem target_J_all (i j : Basis) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j := by
  simpa only [material] using target_linear_J i j

theorem parent_same_source (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    material.parent.combinedTargetJ i j = material.combinedTargetJ i j := by
  simpa only [material, High.material] using
    (High.target_J_all_source i j hi hj).symm.trans (target_linear_J i j)

structure Closure : Prop where
  parent : High.Closure
  fifthMoment : type_of% raw_moment_five
  linearPolynomial : type_of% shifted_pair_gaussian_linear_integral
  targetAxis : type_of% target_axis_integral
  spatial : type_of% spatial_target_linear_factor
  originalLinear : type_of% original_target_linear_card
  quartet : type_of% source_target_linear_quartet
  targetClassification : type_of% target_linear_entries_exact
  targetCount : type_of% target_linear_entries_card
  targetAll : type_of% target_linear_J
  parentIdentity : type_of% parent_identity
  installedTargetCount : type_of% analytic_target_count
  installedQuartet : type_of% quartet_exact
  installedJ : type_of% target_J_all
  sameSource : type_of% parent_same_source

theorem sourceGeneratedClosure : Closure :=
  ⟨High.sourceGeneratedClosure,raw_moment_five,
    shifted_pair_gaussian_linear_integral,target_axis_integral,
    spatial_target_linear_factor,original_target_linear_card,
    source_target_linear_quartet,target_linear_entries_exact,
    target_linear_entries_card,target_linear_J,
    parent_identity,analytic_target_count,quartet_exact,target_J_all,
    parent_same_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
