import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaColumn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid SaturationMonoid.PhysicsCore
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa
open SU7ExteriorYukawaMassSpectrum StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open DiracCliffordRepresentation DiracExteriorMatterAction
open SourceQuantumScalarChart SourceQuantumFockGauge GaussYukawaCoefficient
open scoped BigOperators InnerProductSpace Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.InternalIndex := Classical.decEq _

private theorem vacuum_original : scalarCoordinateEquiv.symm vacuum = finiteGenerationJointBreakingScalar := by
  simp [vacuum,sourceGeneratedVacuumCoordinates,positive_sourceGeneratedVacuumBase]

theorem actual_vacuum_primal_entry :
    primal vacuum ⟨1,Sum.inl yukawaOutputA⟩ (rootIndex (3,2,1)) =
      (Stage9C.Material.SpinPair.lapse : ℂ) * yukawaSourcePhase := by
  change (LowEnergy.Quantum.operatorMatrix
    (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm vacuum)))
      ⟨1,Sum.inl yukawaOutputA⟩ (rootIndex (3,2,1)) = _
  rw [vacuum_original]
  change (LinearMap.toMatrix LowEnergy.Quantum.wholeBasis LowEnergy.Quantum.wholeBasis
    (LowEnergy.FullQuantum.yukawaHamiltonian finiteGenerationJointBreakingScalar))
      ⟨1,Sum.inl yukawaOutputA⟩ (rootIndex (3,2,1)) = _
  rw [LinearMap.toMatrix_apply]
  simp only [LowEnergy.Quantum.wholeBasis,Pi.basis_repr,Pi.basis_apply,
    LowEnergy.FullQuantum.yukawaHamiltonian,LinearMap.smul_apply,LinearMap.comp_apply,
    diracDualRightChiralYukawaAction,diracExteriorYukawaInternalAction,internalMatterLinearAction,
    diracMatrixMatterAction,LinearMap.coe_mk,AddHom.coe_mk,
    LowEnergy.Quantum.internalBasis,rootIndex,exteriorYukawaInternalAction]
  norm_num [rightChiralityProjector,diracGammaFive,diracGammaZero,Fin.sum_univ_four,Pi.single_apply,
    Matrix.one_apply,Matrix.diagonal_apply]
  rw [←algebraMap_smul ℂ Stage9C.Material.SpinPair.lapse
    (exteriorYukawaMassMap finiteGenerationJointBreakingScalar (su7ExteriorBasis 2 (internalBasis 2 1))),map_smul]
  change (Stage9C.Material.SpinPair.lapse : ℂ) *
    (su7ExteriorBasis 6).repr (exteriorYukawaMassMap finiteGenerationJointBreakingScalar
      (su7ExteriorBasis 2 (internalBasis 2 1))) yukawaOutputA = _
  rw [actual_vacuum_mass_entry]

end LowEnergy.MixedSpectatorCandidate
