import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyPoleChargeTensor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalEnergyCurrentWardReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance energyWardQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

/-- This is the full original mother Hamiltonian, including its nonselfadjoint Yukawa term. -/
def sourceHamiltonianFiber (p : PhysicalMomentum) : FiberOperators:=operator (FullQuantum.hamiltonian actual 0 p)

theorem sourceCliffordFiber_original (A : DiracMatrix) :
    sourceCliffordFiber A=operator (diracMatrixMatterAction A) := by
  change operator (Quantum.operatorMatrix.symm (Quantum.operatorMatrix (diracMatrixMatterAction A)))=_
  rw [AlgEquiv.symm_apply_apply]

theorem sourcePrincipal_clifford (p : PhysicalMomentum) :
    Electromagnetic.CanonicalCoframe.principalOperator p=
      sourceCliffordFiber (Electromagnetic.CanonicalCoframe.spinPrincipal p) := by
  rw [sourceCliffordFiber_original,Electromagnetic.CanonicalCoframe.principalOperator,
    principal_operator,Electromagnetic.CanonicalCoframe.principalMatrix_spin,spin_operator]

private theorem spinPrincipal_sub (left right : PhysicalMomentum) :
    Electromagnetic.CanonicalCoframe.spinPrincipal (left-right)=
      Electromagnetic.CanonicalCoframe.spinPrincipal left-Electromagnetic.CanonicalCoframe.spinPrincipal right := by
  simp only [Electromagnetic.CanonicalCoframe.spinPrincipal,Pi.sub_apply,Complex.ofReal_sub,
    mul_sub,sub_smul,Finset.sum_sub_distrib]

/-- All source lower terms cancel between the two physical momenta; the full Hamiltonians themselves are unchanged. -/
theorem sourceHamiltonianFiber_difference (left right : PhysicalMomentum) :
    sourceHamiltonianFiber left-sourceHamiltonianFiber right=
      sourceCliffordFiber (Electromagnetic.CanonicalCoframe.spinPrincipal (left-right)) := by
  simp only [sourceHamiltonianFiber,Electromagnetic.CanonicalCoframe.fullHamiltonian_split,
    sourcePrincipal_clifford,spinPrincipal_sub,map_sub]
  abel

theorem sourcePhysicalCurrent_lapse : (Real.sqrt 30:ℂ)/5=(5/3:ℂ)*(lapse:ℂ) := by
  have square : (Real.sqrt 30)^2=((25/3:ℝ)*lapse)^2:=by
    rw [Real.sq_sqrt (by norm_num),mul_pow,lapse_sq]
    norm_num
  have roots : Real.sqrt 30=(25/3:ℝ)*lapse:=
    (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) lapse_pos.le)).mp square
  have real : Real.sqrt 30/5=(5/3:ℝ)*lapse:=by rw [roots];ring
  simpa only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat] using
    congrArg (fun x : ℝ=>(x:ℂ)) real

theorem sourcePrincipalCurrent_generated (n : PhysicalMomentum) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourceCliffordCurrent (Electromagnetic.CanonicalCoframe.spinPrincipal n) shift sideL edgeL sideR edgeR=
      ∑j : Fin 3,(-(lapse:ℂ)*(n j:ℂ))*sourcePhysicalCliffordSpatialCurrent j shift sideL edgeL sideR edgeR := by
  rw [sourceCliffordCurrent_fourier]
  simp only [Electromagnetic.CanonicalCoframe.spinPrincipal,map_sum,map_smul,sum_apply,smul_apply,
    inner_sum,inner_smul_right]
  rw [integral_finsetSum]
  · simp only [integral_const_mul,←sourceCliffordCurrent_fourier,sourcePhysicalCliffordSpatialCurrent]
  · intro j _
    exact (sourceCliffordCurrent_integrable (diracGammaZero*diracGamma j.succ) shift sideL edgeL sideR edgeR).const_mul _

def sourceHamiltonianTransferIntegrand (shift : Position) (sideL edgeL sideR edgeR : Fin 2)
    (frequency : Position) : ℂ :=
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    ((sourceHamiltonianFiber (physicalMomentum frequency)-sourceHamiltonianFiber (physicalMomentum (frequency-shift)))
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))

/-- The same Fourier transfer acts on both original coframe Hamiltonians. -/
theorem sourceHamiltonianTransfer_original (shift frequency : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceHamiltonianTransferIntegrand shift sideL edgeL sideR edgeR frequency=
      inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (sourceCliffordFiber (Electromagnetic.CanonicalCoframe.spinPrincipal (physicalMomentum shift))
          (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  have momentum : physicalMomentum frequency-physicalMomentum (frequency-shift)=physicalMomentum shift := by
    ext j
    simp only [physicalMomentum,Pi.sub_apply,PiLp.sub_apply]
    ring
  rw [sourceHamiltonianTransferIntegrand,sourceHamiltonianFiber_difference,momentum]

theorem sourceHamiltonianTransfer_integrable (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceHamiltonianTransferIntegrand shift sideL edgeL sideR edgeR) volume := by
  apply (sourceCliffordCurrent_integrable (Electromagnetic.CanonicalCoframe.spinPrincipal (physicalMomentum shift))
    shift sideL edgeL sideR edgeR).congr
  exact Filter.Eventually.of_forall (fun frequency=>(sourceHamiltonianTransfer_original shift frequency sideL edgeL sideR edgeR).symm)

/-- The complete spatial-current remainder is the original Hamiltonian transfer, with its source-generated normalization. -/
theorem sourceEnergySpatialRemainder_hamiltonian (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceEnergySpatialRemainder shift sideL edgeL sideR edgeR=
      (-(5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
        ∫frequency : Position,sourceHamiltonianTransferIntegrand shift sideL edgeL sideR edgeR frequency := by
  simp_rw [sourceHamiltonianTransfer_original]
  rw [←sourceCliffordCurrent_fourier,sourcePrincipalCurrent_generated]
  unfold sourceEnergySpatialRemainder
  have scalar : (ActionNormalization.phaseMomentum:ℂ)*(Real.sqrt 30:ℂ)/5=
      (ActionNormalization.phaseMomentum:ℂ)*((5/3:ℂ)*(lapse:ℂ)):=by
    rw [mul_div_assoc,sourcePhysicalCurrent_lapse]
  rw [scalar]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceEnergyChannel_two_hamiltonian (shift : Position) (frequency : ℝ)
    (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 2 sideL edgeL sideR edgeR=
      (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR-
        ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
          ∫k : Position,sourceHamiltonianTransferIntegrand shift sideL edgeL sideR edgeR k := by
  have generated:=sourcePhysicalEnergyChannel_two_charge shift frequency sideL edgeL sideR edgeR
  change (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 2 sideL edgeL sideR edgeR=
    (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR+sourceEnergySpatialRemainder shift sideL edgeL sideR edgeR at generated
  rw [generated,sourceEnergySpatialRemainder_hamiltonian]
  ring

end LowEnergy.PreparationPhysicalEnergyCurrentWardReturn
