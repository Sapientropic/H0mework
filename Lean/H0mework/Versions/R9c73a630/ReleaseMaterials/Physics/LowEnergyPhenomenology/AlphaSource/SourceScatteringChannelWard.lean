import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceScatteringFrequencyEnergy

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalScatteringFrequencyWard
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
local instance scatteringVertexQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

/-- The complete source identity at all physical probe momenta fixes all four frequency coefficients. -/
theorem sourceScatteringChannelTwo_coefficients (n : PhysicalMomentum) (zeta : ℂ) (k : Fin 4) :
    complexFrequencyCoefficients (originalComplexDirection (sourceChargedChannel n zeta 2)) k=
      if k=0 then sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n zeta)) else 0 := by
  have zeroScalar (T : FiberOperators) : (0:ℂ) • T=0:=zero_smul ℂ T
  have oneScalar (T : FiberOperators) : (1:ℂ) • T=T:=one_smul ℂ T
  have zero:=sourceScatteringFrequency_two (0:PhysicalMomentum) n zeta
  simp only [affine,Pi.zero_apply,Complex.ofReal_zero,zeroScalar,Finset.sum_const_zero,add_zero] at zero
  cases k using Fin.cases
  · simpa only [ite_true] using zero
  · rename_i j
    have axis:=sourceScatteringFrequency_two (Pi.single j 1) n zeta
    simp only [affine,Pi.single_apply,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,
      ite_smul,oneScalar,zeroScalar,Finset.sum_ite_eq',Finset.mem_univ,if_true] at axis
    rw [zero] at axis
    simpa only [Fin.succ_ne_zero,ite_false] using add_eq_left.mp axis

/-- The source-generated temporal and spatial Clifford coefficients are the full original Hamiltonian transfer. -/
theorem sourceScatteringChannelTwo_hamiltonian (left right : PhysicalMomentum) (frequency : ℝ) :
    sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum (left-right) (Complex.I*(frequency:ℂ))))=
      (-(frequency:ℂ)) • (1:FiberOperators)-(5/3:ℂ) •
        (sourceHamiltonianFiber left-sourceHamiltonianFiber right) := by
  rw [sourceHamiltonianFiber_difference,←sourceCliffordFiber_one]
  simp only [←map_smul,←map_sub]
  apply congrArg sourceCliffordFiber
  have temporal : Complex.I*(Complex.I*(frequency:ℂ))= -(frequency:ℂ) := by
    rw [←mul_assoc,Complex.I_mul_I,neg_one_mul]
  simp only [sourcePhysicalChannelTwoClifford,fixedMomentum,fullMomentum,physicalSpatial,
    Fin.cases_zero,Fin.cases_succ,temporal,Electromagnetic.CanonicalCoframe.spinPrincipal,
    Finset.smul_sum,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have coefficient:=sourcePhysicalCurrent_lapse
  calc
    (Complex.I*(Real.sqrt 30:ℂ)/5)*(Complex.I*((left-right) j:ℂ))=
      -((Real.sqrt 30:ℂ)/5)*((left-right) j:ℂ) := by
        rw [div_eq_mul_inv]
        ring_nf
        simp only [Complex.I_sq]
        ring
    _=(5/3:ℂ)*(-(lapse:ℂ)*((left-right) j:ℂ)) := by rw [coefficient];ring

/-- The original scattering vertex is read between actual full Dirac Green legs, with independent spectral data retained. -/
theorem sourceScatteringChannelTwo_fullWard (left right : PhysicalMomentum) (frequency : ℝ)
    (energyL dampingL energyR dampingR : ℝ) (positiveL : 0<dampingL) (positiveR : 0<dampingR) :
    (Retarded.diracValue 0 left energyL dampingL).adjoint*
      complexFrequencyCoefficients (originalComplexDirection
        (sourceChargedChannel (left-right) (Complex.I*(frequency:ℂ)) 2)) 0*
      Retarded.diracValue 0 right energyR dampingR=
      (-(frequency:ℂ)-(5/3:ℂ)*(star (Retarded.spectralParameter energyL dampingL)-
        Retarded.spectralParameter energyR dampingR)) •
        ((Retarded.diracValue 0 left energyL dampingL).adjoint*Retarded.diracValue 0 right energyR dampingR)-
      (5*Complex.I/3) • (sourceEnergyTemporalInverse.adjoint*Retarded.diracValue 0 right energyR dampingR)-
      (5*Complex.I/3) • ((Retarded.diracValue 0 left energyL dampingL).adjoint*sourceEnergyTemporalInverse)-
      (5/3:ℂ) • ((Retarded.diracValue 0 left energyL dampingL).adjoint*sourceEnergyYukawaDefect*
        Retarded.diracValue 0 right energyR dampingR) := by
  rw [sourceScatteringChannelTwo_coefficients,if_pos rfl,sourceScatteringChannelTwo_hamiltonian]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one]
  have ward:=sourceEnergyDiracWard left right energyL dampingL energyR dampingR positiveL positiveR
  simp only [mul_sub,sub_mul] at ward
  rw [ward]
  module

end LowEnergy.PreparationPhysicalScatteringFrequencyWard
