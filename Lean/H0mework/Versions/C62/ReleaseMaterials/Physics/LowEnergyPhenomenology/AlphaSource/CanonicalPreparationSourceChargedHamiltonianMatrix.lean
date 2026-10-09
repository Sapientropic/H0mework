import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedHamiltonianFourier
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNormalizedEnergyJet

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedHamiltonianRead
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9C.Material.SpinPair
open FullQuantum FullSpace YangMills.FullPairing Electromagnetic.CanonicalCoframe
open FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization PreparationVacuumVoltageGaussGreen
open PreparationPhysicalNormalizedFullField PreparationVacuumMovingPoleGaussReturn
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussFockLift GaussQuantumMultiplier
open CanonicalGradedCharge CanonicalGradedSpatialSource GaussHistoryHilbert
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _

/-- The fixed source state's four coefficients are exactly the original full 252-dimensional Hamiltonian. -/
theorem sourceActualHamiltonian_matrix (p : PhysicalMomentum) :
    affineMatrix (stateHamiltonian sourceVoltageActualState) p=
      Quantum.operatorMatrix (FullQuantum.hamiltonian actual 0 p) := by
  simp only [sourceVoltageActualState,affineMatrix,stateHamiltonian_event,
    sourceHamiltonianCoefficients,Fin.cases_zero,Fin.cases_succ]
  rw [←coframeHamiltonian_affine,coframeHamiltonian_actual]

private theorem natural_coordinates (v : DiracExteriorMatterAction.DiracExteriorMatterCarrier)
    (index : Quantum.Index) : Quantum.coordinates v index=naturalCoordinates v (index.1,index.2) := by
  rcases index with ⟨spin,sector⟩
  rfl

private theorem matrix_pair (A : SourceMatrix)
    (u v : DiracExteriorMatterAction.DiracExteriorMatterCarrier) :
    (∑i : Quantum.Index,star (Quantum.coordinates u i)*(A*ᵥQuantum.coordinates v) i)=
      inner ℂ (naturalCoordinates u) (operator (Quantum.operatorMatrix.symm A) (naturalCoordinates v)) := by
  rw [operator_coordinates,EuclideanSpace.inner_eq_star_dotProduct]
  have action:=Quantum.matrix_action (Quantum.operatorMatrix.symm A) v
  rw [Quantum.operatorMatrix.apply_symm_apply] at action
  rw [action]
  simp only [dotProduct,natural_coordinates,Fintype.sum_sigma,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private theorem gauss_fourier_pair (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (A : Fin 4→SourceMatrix) (side edge other opposite : Fin 2) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
      (lift (quantized (fourierLinear p A)) (sourceChargedGaussPrepared epsilon precision other opposite))=
      inner ℂ (naturalCoordinates (sourceChargedRestriction side edge))
        (operator (Quantum.operatorMatrix.symm (affineMatrix A p))
          (naturalCoordinates (sourceChargedRestriction other opposite))) := by
  have base : inner ℂ (sourcePoleBase epsilon precision) (sourcePoleBase epsilon precision)=1 := by
    rw [inner_self_eq_norm_sq_to_K,sourcePoleBase_unit]
    norm_num
  rw [←GaussHalfDensity.fockHalfDensityEquiv.inner_map_map,PiLp.inner_apply]
  simp only [sourceChargedGaussPrepared_coordinates,sourceChargedGauss_action_coordinates,
    inner_smul_left,inner_smul_right,base,mul_one]
  change inner ℂ (sourceChargedFiber side edge) (quantized (fourierLinear p A) (sourceChargedFiber other opposite))=_
  rw [sourceChargedFiber,sourceChargedFiber,quantized_oneParticle,SourceQuantumFockGauge.fiber_pairing]
  simp only [oneParticleFiber,LinearEquiv.apply_symm_apply]
  rw [QuantizationCheck.Fermion.pairing_oneParticle]
  change (∑i : Mode,star (sourceChargedCoordinates side edge i)*
    (realFourierMatrix A p*ᵥsourceChargedCoordinates other opposite) i)=_
  simp only [sourceChargedCoordinates,realFourierMatrix,Matrix.fromBlocks_mulVec,Function.comp_def,
    Sum.elim_inl,Sum.elim_inr,Matrix.zero_mulVec,add_zero,zero_add,
    Fintype.sum_sum_type,star_zero,zero_mul,Finset.sum_const_zero]
  exact matrix_pair _ _ _

/-- Configuration Gauss and physical-space packets read the same original Hamiltonian matrix through the actual maker. -/
theorem sourceActualHamiltonian_Gauss (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (side edge other opposite : Fin 2) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
      (lift (quantized (fourierLinear p (stateHamiltonian sourceVoltageActualState)))
        (sourceChargedGaussPrepared epsilon precision other opposite))=
      inner ℂ (naturalCoordinates (sourceChargedRestriction side edge))
        (operator (FullQuantum.hamiltonian actual 0 p)
          (naturalCoordinates (sourceChargedRestriction other opposite))) := by
  rw [gauss_fourier_pair,sourceActualHamiltonian_matrix,Quantum.operatorMatrix.symm_apply_apply]

/-- The newly generated complete native energy variation is read on the same two independent source preparations. -/
theorem sourceActualEnergyJet_Gauss (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (v : ActionState) (side edge other opposite : Fin 2) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
      (lift (quantized (sourceNormalizedEnergySymbol p sourceVoltageActualState v))
        (sourceChargedGaussPrepared epsilon precision other opposite))=
      inner ℂ (naturalCoordinates (sourceChargedRestriction side edge))
        (operator (Quantum.operatorMatrix.symm
          (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState v) p))
          (naturalCoordinates (sourceChargedRestriction other opposite))) := by
  rw [sourceNormalizedEnergySymbol_matrix p sourceVoltageActualState v
    ⟨coframe_nondegenerate sourcePoint,temporal_noncharacteristic sourcePoint⟩]
  exact gauss_fourier_pair epsilon precision p _ side edge other opposite

/-- The same four source coefficients enter the whole physical Fourier integral of the actual filtered pair. -/
theorem sourceChargedEnergyPair_sourceMatrix (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyPair sideL edgeL sideR edgeR=
      ∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (operator (Quantum.operatorMatrix.symm
          (affineMatrix (stateHamiltonian sourceVoltageActualState) (physicalMomentum frequency)))
          (fourier (sourceChargedFilteredPacket sideR edgeR) frequency)) := by
  simp only [sourceActualHamiltonian_matrix,Quantum.operatorMatrix.symm_apply_apply]
  exact sourceChargedEnergyPair_fourier sideL edgeL sideR edgeR

end LowEnergy.PreparationPhysicalChargedHamiltonianRead
