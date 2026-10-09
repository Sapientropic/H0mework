import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteOriginDiracWard
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceRemainderPoleAssembly
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedNativeEnergyDomain

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteTransferOriginWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalNativePhaseChargeInventory
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedEnergyPoleReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedPacketVoltage
open PreparationPhysicalNormalizedFullField PreparationPhysicalScatteringFrequencyWard
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalElectromagneticDirectionReturn
open PreparationPhysicalRemainderWardPoleReturn PreparationPhysicalChargedVertexDomainReturn
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumVoltageGaussGreen PreparationVacuumSoftPoleSelection
open PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumSourceFieldFamily
open CanonicalGradedSpatialSource
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe
open FullQuantum.CoframeResponse FullQuantum.StateGreen
open MeasureTheory Filter
open scoped Matrix BigOperators InnerProductSpace Topology
attribute [local irreducible] sourceOriginPhaseFiber sourceNativeOriginGeneratorFiber
  sourceHamiltonianFiber sourceEnergyTemporalInverse sourceEnergyYukawaDefect sourceEnergyMatrixRead

/-- The two original filtered inputs retain their own normalizations and the true Fourier transfer. -/
def sourceFiniteOriginWardIntegrand (shift : Position) (sideL edgeL sideR edgeR : Fin 2)
    (frequency : Position) : ℂ :=
  2*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceOriginPhaseFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))-
  Complex.I*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceNativeOriginGeneratorFiber (sourceEnergyTemporalInverse
      (fourier (sourceEnergyInputPacket sideR edgeR) (frequency-shift))))-
  Complex.I*inner ℂ (sourceEnergyTemporalInverse (fourier (sourceEnergyInputPacket sideL edgeL) frequency))
    (sourceNativeOriginGeneratorFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))-
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceEnergyYukawaDefect (sourceNativeOriginGeneratorFiber
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))))+
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    ((sourceHamiltonianFiber (physicalMomentum frequency)-sourceHamiltonianFiber (physicalMomentum (frequency-shift)))
      (sourceNativeOriginGeneratorFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))))

private theorem phase_term (shift : Position) (sideL edgeL sideR edgeR : Fin 2)
    (frequency : Position) :
    (2*Complex.I)*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceNativeOriginGeneratorFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))=
    2*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceOriginPhaseFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  rw [sourceOriginPhaseFiber_generated,smul_apply,inner_smul_right]
  ring

theorem sourceFiniteOriginWard_generated (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (fun frequency : Position=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceEnergyMatrixRead
        (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState
          (fieldDirection (sourceNativeOriginReal 0))) (physicalMomentum (frequency-shift)))
        (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))))=ᵐ[volume]
      sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR := by
  have shifted:=(measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (sourceEnergyFiltered_fourier sideR edgeR)
  filter_upwards [sourceEnergyFiltered_fourier sideL edgeL,shifted] with frequency left right
  have generated:=congrArg (fun A : FiberOperators=>
    inner ℂ (fourier (sourceEnergyInputPacket sideL edgeL) frequency)
      (A (fourier (sourceEnergyInputPacket sideR edgeR) (frequency-shift))))
    (sourceFiniteOriginDiracWard_preparation (physicalMomentum frequency) (physicalMomentum (frequency-shift)))
  simp only [mul_apply_eq_comp,sub_apply,add_apply,smul_apply,inner_sub_right,inner_add_right,
    inner_smul_right,ContinuousLinearMap.adjoint_inner_right] at generated
  simp only [sourceNativeOriginEnergyFiber,sourceFiniteOriginWardIntegrand]
  rw [←phase_term]
  simp only [left,right]
  simpa only [sub_apply,mul_apply_eq_comp,inner_sub_right] using generated

/-- Integrability is paid for the complete Ward expression, without separating unpriced terms. -/
theorem sourceFiniteOriginWard_integrable (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR) volume :=
  (sourceChargedEnergyRead_integrable (fieldDirection (sourceNativeOriginReal 0)) shift
    sideL edgeL sideR edgeR).congr (sourceFiniteOriginWard_generated shift sideL edgeL sideR edgeR)

theorem sourceFiniteOriginEnergy_return (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyRead (fieldDirection (sourceNativeOriginReal 0)) shift sideL edgeL sideR edgeR=
      ∫frequency : Position,sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR frequency := by
  rw [sourceChargedEnergyRead_fourier]
  exact integral_congr_ae (sourceFiniteOriginWard_generated shift sideL edgeL sideR edgeR)

theorem sourceFiniteOriginWard_bound (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ‖∫frequency : Position,sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR frequency‖≤
      sourceEnergyDiracPrice (fieldDirection (sourceNativeOriginReal 0))/‖sourceChargedRawPacket sideR edgeR‖ := by
  rw [←sourceFiniteOriginEnergy_return]
  exact sourceChargedEnergyRead_norm _ shift sideL edgeL sideR edgeR

private theorem field_integrand (V : Fin 289→ℂ) (p : PhysicalMomentum) (u v : YangMills.FullPairing.Hilbert) :
    inner ℂ u (affine (complexFrequencyCoefficients (originalComplexDirection V)) p v)=
      ∑j : Fin 289,V j*inner ℂ u
        (sourceEnergyMatrixRead (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState
          (fieldDirection (fieldUnit j))) p) v) := by
  rw [sourceScatteringFrequency_affine]
  simp only [map_sum,map_smul,sum_apply,smul_apply,inner_sum,inner_smul_right]

private theorem field_fourier (V : Fin 289→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR V=
      ∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (affine (complexFrequencyCoefficients (originalComplexDirection V)) (physicalMomentum (frequency-shift))
          (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  rw [sourcePhysicalEnergyReader_original,sourceFullEnergyRead_generated]
  simp_rw [field_integrand,sourceChargedEnergyRead_fourier]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j _
    exact (sourceChargedEnergyRead_integrable (fieldDirection (fieldUnit j)) shift
      sideL edgeL sideR edgeR).const_mul _

/-- The complete finite origin, including its original field representation, feeds the same energy read. -/
theorem sourceFiniteOriginWholeEnergy_return (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourcePoleOriginField branch epsilon s n)=
      sourceFiniteOriginAmplitude branch epsilon s n*
        ∫frequency : Position,sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR frequency := by
  rw [field_fourier]
  simp only [sourceFiniteOriginHamiltonian_commutator,smul_mul_assoc,mul_smul_comm,
    sub_apply,smul_apply,inner_sub_right,inner_smul_right,←mul_sub]
  rw [integral_const_mul]
  congr 1
  rw [←sourceFiniteOriginEnergy_return,sourceChargedEnergyRead_fourier]
  simp_rw [sourceNativeOriginEnergyFiber,sub_apply,mul_apply_eq_comp,inner_sub_right]

theorem sourceFiniteOriginWholeWard_integrable (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (fun frequency : Position=>sourceFiniteOriginAmplitude branch epsilon s n*
      sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR frequency) volume :=
  (sourceFiniteOriginWard_integrable shift sideL edgeL sideR edgeR).const_mul _

theorem sourceFiniteOriginWholeWard_bound (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourcePoleOriginField branch epsilon s n)‖≤
      ‖sourceFiniteOriginAmplitude branch epsilon s n‖*
        (sourceEnergyDiracPrice (fieldDirection (sourceNativeOriginReal 0))/‖sourceChargedRawPacket sideR edgeR‖) := by
  rw [sourceFiniteOriginWholeEnergy_return,norm_mul]
  exact mul_le_mul_of_nonneg_left (sourceFiniteOriginWard_bound shift sideL edgeL sideR edgeR) (norm_nonneg _)

/-- The actual OtherField consumer receives the same h and physical Fourier shift, with no zero-transfer replacement. -/
theorem sourceFiniteOriginOtherEnergy_return (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) :
    (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
      (sourcePoleOriginField branch epsilon s n) (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceFiniteOriginAmplitude branch epsilon s n*
        ∫frequency : Position,sourceFiniteOriginWardIntegrand (sourcePhotonEnergyShift epsilon n)
          sideL edgeL sideR edgeR frequency := by
  have noCharge : ∀mu : Fin 4,sourceChargedCoefficient (sourcePoleOriginField branch epsilon s n) mu=0 :=
    sourcePoleOriginField_charge branch epsilon s n
  simp only [sourceDirectionOtherEnergy,sourceChargedFieldRemainder,sourceChargedFieldPart,noCharge,
    zero_mul,zero_smul,Finset.sum_const_zero,sub_zero,zero_add]
  rw [sourceFiniteOriginWholeEnergy_return]
  ring

end LowEnergy.PreparationPhysicalFiniteTransferOriginWard
