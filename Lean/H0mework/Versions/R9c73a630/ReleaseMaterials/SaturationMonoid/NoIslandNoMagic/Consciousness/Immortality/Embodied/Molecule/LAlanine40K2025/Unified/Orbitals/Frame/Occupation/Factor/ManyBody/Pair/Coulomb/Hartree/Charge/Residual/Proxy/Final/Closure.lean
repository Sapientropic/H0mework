import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final.Comparison
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceCoulomb
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

structure Material where
  parent : Correction.Material
  originalGammaReal : Matrix Basis Basis ℝ
  occupiedReal : Matrix Basis Basis ℝ
  actualEnvelope : ℝ
  spatialResidualEnvelope : ℝ
  hartreeWeight : ℝ

def material : Material where
  parent := Correction.material
  originalGammaReal := fun i j => (rawGamma i j).re
  occupiedReal := fun i j => 2 * (projector24 i j).re
  actualEnvelope := actualMatrixEnvelope
  spatialResidualEnvelope := residualEnvelope
  hartreeWeight := Interaction.interactionWeight Interaction.d3Matrix +
    Interaction.interactionWeightRight Interaction.occupationMatrix

theorem parent_identity : material.parent = Correction.material := rfl
theorem original_gamma_identity (i j : Basis) :
    material.originalGammaReal i j = (rawGamma i j).re := rfl
theorem occupied_identity (i j : Basis) :
    material.occupiedReal i j = 2 * (projector24 i j).re := rfl
theorem original_gamma_error (i j : Basis) :
    |material.parent.recordedD3 i j - material.originalGammaReal i j| <
      (1 / 10^12 : ℝ) := recorded_original_gamma_real i j
theorem occupied_error (i j : Basis) :
    |material.parent.recordedD3 i j - material.occupiedReal i j| <
      (1 / 10^9 : ℝ) := recorded_projector_entry i j
theorem actual_operator_error :
    ‖complexMatrix (normalizedDensityMatrix - material.parent.recordedD3)‖ ≤
      material.actualEnvelope := Correction.actual_D3_complex_operator_bound
theorem actual_spatial_residual (i j : Basis) :
    |residualMatrix i j| < material.spatialResidualEnvelope := actual_residual_entry i j
theorem original_hartree_energy_residual :
    |Interaction.d3HartreeEnergy - directEnergy.re| ≤
      (1 / 2 : ℝ) * material.spatialResidualEnvelope * material.hartreeWeight :=
  actual_hartree_residual_bound

structure Closure : Prop where
  parent : Correction.Closure
  parentIdentity : type_of% parent_identity
  gammaIdentity : type_of% original_gamma_identity
  occupiedIdentity : type_of% occupied_identity
  gammaError : type_of% original_gamma_error
  occupiedError : type_of% occupied_error
  actualOperator : type_of% actual_operator_error
  spatialResidual : type_of% actual_spatial_residual
  hartreeResidual : type_of% original_hartree_energy_residual

theorem sourceGeneratedClosure : Closure :=
  ⟨Correction.sourceGeneratedClosure,parent_identity,original_gamma_identity,
    occupied_identity,original_gamma_error,occupied_error,actual_operator_error,
    actual_spatial_residual,original_hartree_energy_residual⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
