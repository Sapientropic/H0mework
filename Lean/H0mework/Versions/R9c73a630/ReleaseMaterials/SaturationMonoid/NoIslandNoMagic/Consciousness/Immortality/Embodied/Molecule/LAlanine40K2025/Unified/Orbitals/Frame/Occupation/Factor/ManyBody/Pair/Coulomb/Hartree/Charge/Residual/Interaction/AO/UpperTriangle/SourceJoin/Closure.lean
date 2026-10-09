import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Bound
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def targetAddressedJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (sourceCoefficientAt address : ℝ) *
      electronRepulsion (targetLeft address.val) (targetRight address.val) i j

structure Material where
  parent : UpperTriangle.Material
  targetPair : Fin 4851 → Basis × Basis
  sourceCoefficient : Fin 4851 → ℚ
  reportCoefficient : Fin 4851 → ℚ
  targetJ : Matrix Basis Basis ℝ
  reportWeightedJ : Matrix Basis Basis ℝ
  quartetErrorWeight : Matrix Basis Basis ℝ

def material : Material where
  parent := UpperTriangle.material
  targetPair := targetPair
  sourceCoefficient := sourceCoefficientAt
  reportCoefficient := reportCoefficientAt
  targetJ := Matrix.of targetAddressedJ
  reportWeightedJ := Matrix.of reportWeightedJ
  quartetErrorWeight := Matrix.of quartetErrorWeight

theorem parent_identity : material.parent = UpperTriangle.material := rfl

theorem target_J_exact (i j : Basis) :
    material.targetJ i j = material.parent.upperJ i j := by
  calc
    material.targetJ i j = targetAddressedJ i j := rfl
    _ = UpperTriangle.sourceJUpper i j := (sourceJ_target_row_sum i j).symm
    _ = material.parent.upperJ i j := rfl

theorem target_coefficient_bound (address : Fin 4851) :
    |material.sourceCoefficient address - material.reportCoefficient address| <
      (1 : ℚ) / 10^12 :=
  source_coefficient_report_bound address

theorem target_J_report_bound (i j : Basis) :
    |material.targetJ i j - material.reportWeightedJ i j| ≤
      material.quartetErrorWeight i j := by
  calc
    |material.targetJ i j - material.reportWeightedJ i j| =
        |UpperTriangle.sourceJUpper i j - reportWeightedJ i j| := by
      rw [target_J_exact]
      rfl
    _ ≤ quartetErrorWeight i j := report_weighted_J_error i j
    _ = material.quartetErrorWeight i j := rfl

structure Closure : Prop where
  parent : UpperTriangle.Closure
  sourceSymmetry : type_of% original_D3_AO_symmetric
  rows : type_of% all_target_rows_certified
  addressEquiv : Nonempty (Fin 4851 ≃ UpperTriangle.sourceUpperPairs)
  sourceJ : type_of% sourceJ_target_row_sum
  coefficientBound : type_of% source_coefficient_report_bound
  parentIdentity : type_of% parent_identity
  potential : type_of% target_J_exact
  reportBound : type_of% target_coefficient_bound
  potentialReportBound : type_of% target_J_report_bound

theorem sourceGeneratedClosure : Closure :=
  ⟨UpperTriangle.sourceGeneratedClosure,original_D3_AO_symmetric,
    all_target_rows_certified,⟨targetUpperEquiv⟩,
    sourceJ_target_row_sum,source_coefficient_report_bound,
    parent_identity,target_J_exact,target_coefficient_bound,target_J_report_bound⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
