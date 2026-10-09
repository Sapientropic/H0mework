import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteOriginVertices

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteTransferOriginWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing FullQuantum.Triangular
open Stage10.CanonicalMatter
open CanonicalGradedSpatialSource
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalNativePhaseChargeInventory
open Electromagnetic.CanonicalCoframe
open scoped Matrix InnerProductSpace

/-- The original full phase charge, without replacing it by a native gauge action. -/
def sourceOriginPhaseFiber : FiberOperators := operator (phaseInverse.comp sourcePhaseNoether)

theorem sourceOriginPhaseFiber_generated :
    sourceOriginPhaseFiber=Complex.I • sourceNativeOriginGeneratorFiber := by
  exact (congrArg operator sourcePhaseNoether_canonical).trans (operator_smul _ _)

attribute [local irreducible] sourceNativeOriginGeneratorFiber sourceHamiltonianFiber
  sourceEnergyTemporalInverse sourceEnergyYukawaDefect

/-- Independent spectral data and momenta retain the actual transfer term and both Dirac inputs. -/
theorem sourceFiniteOriginDiracWard (left right : PhysicalMomentum)
    (energyL dampingL energyR dampingR : ℝ) (positiveL : 0<dampingL) (positiveR : 0<dampingR) :
    (Retarded.diracValue 0 left energyL dampingL).adjoint*
      (sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber right-
        sourceHamiltonianFiber right*sourceNativeOriginGeneratorFiber)*
          Retarded.diracValue 0 right energyR dampingR=
      (Retarded.spectralParameter energyR dampingR-star (Retarded.spectralParameter energyL dampingL)) •
        ((Retarded.diracValue 0 left energyL dampingL).adjoint*
          sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 right energyR dampingR)-
      Complex.I • ((Retarded.diracValue 0 left energyL dampingL).adjoint*
        sourceNativeOriginGeneratorFiber*sourceEnergyTemporalInverse)-
      Complex.I • (sourceEnergyTemporalInverse.adjoint*sourceNativeOriginGeneratorFiber*
        Retarded.diracValue 0 right energyR dampingR)-
      (Retarded.diracValue 0 left energyL dampingL).adjoint*sourceEnergyYukawaDefect*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 right energyR dampingR+
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber left-sourceHamiltonianFiber right)*sourceNativeOriginGeneratorFiber*
          Retarded.diracValue 0 right energyR dampingR := by
  have split :
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber right-
          sourceHamiltonianFiber right*sourceNativeOriginGeneratorFiber)*
            Retarded.diracValue 0 right energyR dampingR=
      (Retarded.diracValue 0 left energyL dampingL).adjoint*sourceNativeOriginGeneratorFiber*
        (sourceHamiltonianFiber right*Retarded.diracValue 0 right energyR dampingR)-
      ((Retarded.diracValue 0 left energyL dampingL).adjoint*(sourceHamiltonianFiber left).adjoint)*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 right energyR dampingR-
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber left-(sourceHamiltonianFiber left).adjoint)*
          sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 right energyR dampingR+
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber left-sourceHamiltonianFiber right)*sourceNativeOriginGeneratorFiber*
          Retarded.diracValue 0 right energyR dampingR := by noncomm_ring
  rw [split,sourceEnergyDiracGreen_hamiltonian right energyR dampingR positiveR,
    sourceEnergyDiracGreen_dual left energyL dampingL positiveL,sourceHamiltonianFiber_dual_defect]
  simp only [mul_sub,add_mul,smul_mul_assoc,mul_smul_comm,sub_smul,mul_assoc]
  abel

theorem sourceFiniteOriginDiracWard_preparation (left right : PhysicalMomentum) :
    (Retarded.diracValue 0 left 0 1).adjoint*
      (sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber right-
        sourceHamiltonianFiber right*sourceNativeOriginGeneratorFiber)*Retarded.diracValue 0 right 0 1=
      (2*Complex.I) • ((Retarded.diracValue 0 left 0 1).adjoint*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 right 0 1)-
      Complex.I • ((Retarded.diracValue 0 left 0 1).adjoint*
        sourceNativeOriginGeneratorFiber*sourceEnergyTemporalInverse)-
      Complex.I • (sourceEnergyTemporalInverse.adjoint*sourceNativeOriginGeneratorFiber*
        Retarded.diracValue 0 right 0 1)-
      (Retarded.diracValue 0 left 0 1).adjoint*sourceEnergyYukawaDefect*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 right 0 1+
      (Retarded.diracValue 0 left 0 1).adjoint*
        (sourceHamiltonianFiber left-sourceHamiltonianFiber right)*sourceNativeOriginGeneratorFiber*
          Retarded.diracValue 0 right 0 1 := by
  have generated:=sourceFiniteOriginDiracWard left right 0 1 0 1 (by norm_num) (by norm_num)
  have coefficient : Retarded.spectralParameter 0 1-star (Retarded.spectralParameter 0 1)=2*Complex.I := by
    simp only [Retarded.spectralParameter,Complex.ofReal_zero,Complex.ofReal_one,mul_one,zero_add,
      Complex.star_def,Complex.conj_I]
    ring
  rw [coefficient] at generated
  exact generated

end LowEnergy.PreparationPhysicalFiniteTransferOriginWard
