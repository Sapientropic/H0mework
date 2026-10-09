import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyHamiltonianTransfer

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
local instance energyDiracWardQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open StageNineCurrentCoframeMatterTemporalPrincipal

/-- The same original temporal inverse that occurs on the right of the actual Dirac Green operator. -/
def sourceEnergyTemporalInverse : FiberOperators:=
  operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0))

/-- The complete nonselfadjoint source contribution is retained in the independent dual Ward term. -/
def sourceEnergyYukawaDefect : FiberOperators:=
  operator (interactionHamiltonian actual 0)-(operator (interactionHamiltonian actual 0)).adjoint

theorem sourceHamiltonianFiber_dual_defect (p : PhysicalMomentum) :
    sourceHamiltonianFiber p-(sourceHamiltonianFiber p).adjoint=sourceEnergyYukawaDefect := by
  have spin : (operator spinMother).adjoint=operator spinMother:=source_spin_selfAdjoint
  have gauge : (operator gaugeMother).adjoint=operator gaugeMother:=source_gauge_selfAdjoint
  simp only [sourceHamiltonianFiber,Electromagnetic.CanonicalCoframe.fullHamiltonian_split,
    Electromagnetic.CanonicalCoframe.sourceConstant,map_add,
    Electromagnetic.CanonicalCoframe.principalOperator_selfAdjoint,spin,gauge,sourceEnergyYukawaDefect]
  abel

/-- The original causal inverse gives its Hamiltonian source term, with i and C0 inverse in their actual order. -/
theorem sourceEnergyDiracGreen_hamiltonian (p : PhysicalMomentum) (energy damping : ℝ) (positive : 0<damping) :
    sourceHamiltonianFiber p*Retarded.diracValue 0 p energy damping=
      Retarded.spectralParameter energy damping • Retarded.diracValue 0 p energy damping-
        Complex.I • sourceEnergyTemporalInverse := by
  have inverse:=Retarded.value_kernel_left 0 p energy damping positive
  rw [Retarded.kernel_original] at inverse
  change (Retarded.spectralParameter energy damping • (1:FiberOperators)-sourceHamiltonianFiber p)*
    Retarded.value 0 p energy damping=Complex.I • (1:FiberOperators) at inverse
  simp only [sub_mul,smul_mul_assoc,one_mul] at inverse
  have generated : sourceHamiltonianFiber p*Retarded.value 0 p energy damping=
      Retarded.spectralParameter energy damping • Retarded.value 0 p energy damping-Complex.I • (1:FiberOperators) := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp inverse).symm
  simp only [Retarded.diracValue_side 0 p energy damping positive,←mul_assoc,generated,
    sub_mul,smul_mul_assoc,one_mul,sourceEnergyTemporalInverse]

theorem sourceEnergyDiracGreen_dual (p : PhysicalMomentum) (energy damping : ℝ) (positive : 0<damping) :
    (Retarded.diracValue 0 p energy damping).adjoint*(sourceHamiltonianFiber p).adjoint=
      star (Retarded.spectralParameter energy damping) • (Retarded.diracValue 0 p energy damping).adjoint+
        Complex.I • sourceEnergyTemporalInverse.adjoint := by
  have source:=congrArg star (sourceEnergyDiracGreen_hamiltonian p energy damping positive)
  simpa only [star_mul,ContinuousLinearMap.star_eq_adjoint,map_sub,map_smulₛₗ,
    Complex.star_def,Complex.conj_I,neg_smul,sub_neg_eq_add] using source

/-- Independent left/right spectral data retain damping, the actual input legs and the full Yukawa anti-Hermitian term. -/
theorem sourceEnergyDiracWard (left right : PhysicalMomentum) (energyL dampingL energyR dampingR : ℝ)
    (positiveL : 0<dampingL) (positiveR : 0<dampingR) :
    (Retarded.diracValue 0 left energyL dampingL).adjoint*
      (sourceHamiltonianFiber left-sourceHamiltonianFiber right)*Retarded.diracValue 0 right energyR dampingR=
      (star (Retarded.spectralParameter energyL dampingL)-Retarded.spectralParameter energyR dampingR) •
        ((Retarded.diracValue 0 left energyL dampingL).adjoint*Retarded.diracValue 0 right energyR dampingR)+
      Complex.I • (sourceEnergyTemporalInverse.adjoint*Retarded.diracValue 0 right energyR dampingR)+
      Complex.I • ((Retarded.diracValue 0 left energyL dampingL).adjoint*sourceEnergyTemporalInverse)+
      (Retarded.diracValue 0 left energyL dampingL).adjoint*sourceEnergyYukawaDefect*
        Retarded.diracValue 0 right energyR dampingR := by
  have split :
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber left-sourceHamiltonianFiber right)*Retarded.diracValue 0 right energyR dampingR=
      ((Retarded.diracValue 0 left energyL dampingL).adjoint*(sourceHamiltonianFiber left).adjoint)*
        Retarded.diracValue 0 right energyR dampingR-
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber right*Retarded.diracValue 0 right energyR dampingR)+
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber left-(sourceHamiltonianFiber left).adjoint)*Retarded.diracValue 0 right energyR dampingR := by
    noncomm_ring
  rw [split,sourceEnergyDiracGreen_dual left energyL dampingL positiveL,
    sourceEnergyDiracGreen_hamiltonian right energyR dampingR positiveR,sourceHamiltonianFiber_dual_defect]
  simp only [add_mul,mul_sub,smul_mul_assoc,mul_smul_comm,sub_smul]
  abel

/-- The actual preparation filter has energy zero and damping one on both independent legs. -/
theorem sourceEnergyDiracWard_preparation (left right : PhysicalMomentum) :
    (Retarded.diracValue 0 left 0 1).adjoint*
      (sourceHamiltonianFiber left-sourceHamiltonianFiber right)*Retarded.diracValue 0 right 0 1=
      (-2*Complex.I) • ((Retarded.diracValue 0 left 0 1).adjoint*Retarded.diracValue 0 right 0 1)+
      Complex.I • (sourceEnergyTemporalInverse.adjoint*Retarded.diracValue 0 right 0 1)+
      Complex.I • ((Retarded.diracValue 0 left 0 1).adjoint*sourceEnergyTemporalInverse)+
      (Retarded.diracValue 0 left 0 1).adjoint*sourceEnergyYukawaDefect*Retarded.diracValue 0 right 0 1 := by
  have source:=sourceEnergyDiracWard left right 0 1 0 1 (by norm_num) (by norm_num)
  have coefficient : star (Retarded.spectralParameter 0 1)-Retarded.spectralParameter 0 1= -2*Complex.I := by
    simp only [Retarded.spectralParameter,Complex.ofReal_zero,Complex.ofReal_one,mul_one,zero_add,
      Complex.star_def,Complex.conj_I]
    ring
  rw [coefficient] at source
  exact source

end LowEnergy.PreparationPhysicalEnergyCurrentWardReturn
