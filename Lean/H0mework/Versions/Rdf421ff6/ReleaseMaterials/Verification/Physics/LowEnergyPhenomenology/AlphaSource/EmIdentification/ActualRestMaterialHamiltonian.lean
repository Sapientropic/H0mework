import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightWholePartition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMaterialClockReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 YangMills.FullPairing
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreHilbert GaussQuantumMultiplier ActualSourcePreparationBridge
open PreparationVacuumElectromagneticIdentity PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily FullQuantum.StateGreen
open Electromagnetic.CanonicalCoframe FullQuantum.CoframeResponse
open CanonicalGradedSpatialSource
open scoped Matrix BigOperators InnerProductSpace
attribute [local irreducible] actualRestStatePreparation sourceState

/-- The primal part of the original doubled material symbol reads the original full mother Hamiltonian, at the actual source point. -/
theorem source_material_primal_hamiltonian (p : PhysicalMomentum) :
    (sourceHamiltonianMaterial p GaussHistoryHilbert.sourcePoint.val).toBlocks₁₁=
      Quantum.operatorMatrix (FullQuantum.hamiltonian Stage9C.Material.SpinPair.actual 0 p) := by
  change affineMatrix (stateHamiltonian (sourceState GaussHistoryHilbert.sourcePoint.val)) p=_
  simp only [affineMatrix,stateHamiltonian_event,sourceHamiltonianCoefficients,
    Fin.cases_zero,Fin.cases_succ]
  rw [←coframeHamiltonian_affine,coframeHamiltonian_actual]

private theorem primal_rest_pair (side : Fin 2) (row column : Fin 4) (p : PhysicalMomentum) :
    (∑i : Quantum.Index,star (restPrimalWave (side,row) i)*
      (Quantum.operatorMatrix (FullQuantum.hamiltonian Stage9C.Material.SpinPair.actual 0 p)*ᵥ
        restPrimalWave (side,column)) i)=actualMatterCarrierHamiltonian 0 side p row column := by
  unfold restPrimalWave
  rw [Quantum.matrix_action]
  change Quantum.coordinatePair _ _=_
  rw [Quantum.coordinatePair_full,←YangMills.FullPairing.natural_inner]
  rw [←operator_coordinates]
  simp only [LinearEquiv.apply_symm_apply]
  unfold actualMatterCarrierHamiltonian
  rw [Runtime.configuration_eq]

/-- The true source preparation columns, rather than a free embedding, restrict both original momenta to the matching four-state Hamiltonian. -/
theorem source_rest_primal_hamiltonian (side : Fin 2) (p : PhysicalMomentum) :
    restBlockRestriction (false,side) (sourceHamiltonianMaterial p GaussHistoryHilbert.sourcePoint.val)=
      actualMatterCarrierHamiltonian 0 side p := by
  ext row column
  unfold restBlockRestriction
  rw [Matrix.mul_assoc]
  change (∑i : Mode,star (restModeWave false (side,row) i)*
    (∑j : Mode,sourceHamiltonianMaterial p GaussHistoryHilbert.sourcePoint.val i j*
      restModeWave false (side,column) j))=_
  simp only [restModeWave,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,
    if_false,star_zero,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
  have primal (i j : Quantum.Index) : sourceHamiltonianMaterial p GaussHistoryHilbert.sourcePoint.val
      (.inl i) (.inl j)=Quantum.operatorMatrix (FullQuantum.hamiltonian Stage9C.Material.SpinPair.actual 0 p) i j :=
    congrFun (congrFun (source_material_primal_hamiltonian p) i) j
  simp only [primal]
  exact primal_rest_pair side row column p

end LowEnergy.GaussComposite.ActualSourceLightCircuit
