import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Column

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceFiniteData
open scoped BigOperators
noncomputable section

structure Material where
  parent : SourceJoin.Material
  pairMajorantTable : Basis → Basis → ℚ
  sumBound : ℚ
  amaxBound : ℚ
  sourceBound : ℚ
  reportBound : ℚ
  hartreeBound : ℚ
  hartreeNanoBound : ℕ
  reportHartree : ℝ
  reportPotentialResidual : ℝ
  columnQuantization : ℚ
  outerEndpoint : ℝ → ℝ → ℝ → ℝ

def material : Material where
  parent := SourceJoin.material
  pairMajorantTable := pairMajorant
  sumBound := sumBound
  amaxBound := amaxBound
  sourceBound := sourceBound
  reportBound := reportBound
  hartreeBound := hartreeBound
  hartreeNanoBound := hartreeNanoBound
  reportHartree := reportHartreeEnergy
  reportPotentialResidual := reportPotentialResidual
  columnQuantization := coulombColumnQuantization
  outerEndpoint := endpointAntiderivative

theorem parent_identity : material.parent = SourceJoin.material := rfl

structure Closure : Prop where
  parent : SourceJoin.Closure
  endpointZero : type_of% endpointAntiderivative_zero
  endpointOne : type_of% endpointAntiderivative_one
  outerIntegral : type_of% outerMajorant_integral
  majorant : type_of% electron_repulsion_majorant
  blockTable : type_of% addressMajorant_total_sum
  perQuartetWeight : type_of% quartet_error_weight_le
  weightSymmetric : type_of% quartetErrorWeight_symm
  uniformWeight : type_of% quartet_error_weight_uniform
  reportJ : type_of% report_J_replacement
  reportJpico : type_of% report_J_replacement_picohartree
  d3Address : type_of% d3_hartree_address
  replacement : type_of% blyp_coulomb_replacement
  nanoBound : type_of% blyp_coulomb_nanohartree
  nanoLt : type_of% hartreeNanoBound_lt
  columnReadout : type_of% coulomb_column_readout
  columnValue : type_of% coulombColumnQuantization_value
  blypColumn : type_of% blyp_coulomb_column
  blypIntegral : type_of% blyp_coulomb_integral
  parentIdentity : type_of% parent_identity

theorem sourceGeneratedClosure : Closure :=
  ⟨SourceJoin.sourceGeneratedClosure,endpointAntiderivative_zero,
    endpointAntiderivative_one,outerMajorant_integral,electron_repulsion_majorant,
    addressMajorant_total_sum,quartet_error_weight_le,quartetErrorWeight_symm,
    quartet_error_weight_uniform,report_J_replacement,
    report_J_replacement_picohartree,d3_hartree_address,blyp_coulomb_replacement,
    blyp_coulomb_nanohartree,hartreeNanoBound_lt,coulomb_column_readout,
    coulombColumnQuantization_value,blyp_coulomb_column,blyp_coulomb_integral,
    parent_identity⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
