import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteOriginPreparedReturn
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceInternalSignedEmitter

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalInternalOriginPoleAssembly
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace YangMills.FullPairing CanonicalGradedSpatialSource
open PreparationPhysicalFiniteTransferOriginWard PreparationPhysicalInternalChargePoleReturn
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedPacketVoltage
open PreparationPhysicalNativePoleChargeReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumMixedFieldReturn
open Filter MeasureTheory
open scoped BigOperators InnerProductSpace Topology Matrix
attribute [local irreducible] sourceOriginPhaseFiber sourceNativeOriginGeneratorFiber
  sourceHamiltonianFiber sourceEnergyTemporalInverse sourceEnergyYukawaDefect

def sourceOriginPhasePair (shift : Position) (sideL edgeL sideR edgeR : Fin 2) (k : Position) : ℂ :=
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
    (sourceOriginPhaseFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (k-shift)))

private theorem phase_fourier (shift : Position) (side edge : Fin 2) :
    fourier (sourceInternalPhaseSpatial (PacketNoise.phaseShift shift (sourceChargedFilteredPacket side edge)))=ᵐ[volume]
      fun k : Position=>sourceOriginPhaseFiber (fourier (sourceChargedFilteredPacket side edge) (k-shift)) := by
  have same : sourceInternalPhaseSpatial=sourceOriginPhaseFiber.compLpL 2 volume := by
    unfold sourceInternalPhaseSpatial sourceOriginPhaseFiber
    rfl
  rw [same,GaugeGreen.constant_fourier,PacketNoise.phaseShift_fourier]
  filter_upwards [sourceOriginPhaseFiber.coeFn_compLpL
    (PacketNoise.frequencyShift shift (fourier (sourceChargedFilteredPacket side edge))),
    PacketNoise.frequencyShift_ae shift (fourier (sourceChargedFilteredPacket side edge))] with k reader shifted
  rw [reader,shifted]

theorem sourceOriginPhasePair_integrable (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceOriginPhasePair shift sideL edgeL sideR edgeR) volume := by
  apply (L2.integrable_inner (𝕜:=ℂ) (fourier (sourceChargedFilteredPacket sideL edgeL))
    (fourier (sourceInternalPhaseSpatial (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR))))).congr
  filter_upwards [phase_fourier shift sideR edgeR] with k reader
  simp only [sourceOriginPhasePair,reader]

theorem sourceInternalPhaseFormFactor_integral (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR=
      (ActionNormalization.phaseMomentum:ℂ)*∫k : Position,sourceOriginPhasePair shift sideL edgeL sideR edgeR k := by
  rw [sourceInternalPhaseFormFactor,sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [←fourier.inner_map_map,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [phase_fourier shift sideR edgeR] with k reader
  simp only [sourceOriginPhasePair,reader]

theorem sourceOriginPhasePair_return (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (∫k : Position,sourceOriginPhasePair shift sideL edgeL sideR edgeR k)=
      sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR/(ActionNormalization.phaseMomentum:ℂ) := by
  have nonzero : (ActionNormalization.phaseMomentum:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr ActionNormalization.phaseMomentum_positive.ne'
  apply (eq_div_iff nonzero).2
  rw [mul_comm,sourceInternalPhaseFormFactor_integral]

/-- All original non-charge terms remain together, including the ordered finite momentum transfer. -/
def sourceOriginWardBalance (shift : Position) (sideL edgeL sideR edgeR : Fin 2) (k : Position) : ℂ :=
  -Complex.I*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
    (sourceNativeOriginGeneratorFiber (sourceEnergyTemporalInverse
      (fourier (sourceEnergyInputPacket sideR edgeR) (k-shift))))-
  Complex.I*inner ℂ (sourceEnergyTemporalInverse (fourier (sourceEnergyInputPacket sideL edgeL) k))
    (sourceNativeOriginGeneratorFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (k-shift)))-
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
    (sourceEnergyYukawaDefect (sourceNativeOriginGeneratorFiber
      (fourier (sourceChargedFilteredPacket sideR edgeR) (k-shift))))+
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
    ((sourceHamiltonianFiber (physicalMomentum k)-sourceHamiltonianFiber (physicalMomentum (k-shift)))
      (sourceNativeOriginGeneratorFiber (fourier (sourceChargedFilteredPacket sideR edgeR) (k-shift))))

theorem sourceOriginWardBalance_generated (shift : Position) (sideL edgeL sideR edgeR : Fin 2) (k : Position) :
    sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR k=
      2*sourceOriginPhasePair shift sideL edgeL sideR edgeR k+sourceOriginWardBalance shift sideL edgeL sideR edgeR k := by
  simp only [sourceFiniteOriginWardIntegrand,sourceOriginPhasePair,sourceOriginWardBalance]
  ring

theorem sourceOriginWardBalance_integrable (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceOriginWardBalance shift sideL edgeL sideR edgeR) volume := by
  have price:=(sourceFiniteOriginWard_integrable shift sideL edgeL sideR edgeR).sub
    ((sourceOriginPhasePair_integrable shift sideL edgeL sideR edgeR).const_mul 2)
  apply price.congr
  exact Eventually.of_forall (fun k=>by simp only [Pi.sub_apply,sourceOriginWardBalance_generated]; ring)

theorem sourceOriginWard_integral (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*(∫k : Position,sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR k)=
      2*sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*(∫k : Position,sourceOriginWardBalance shift sideL edgeL sideR edgeR k) := by
  simp_rw [sourceOriginWardBalance_generated]
  rw [integral_add ((sourceOriginPhasePair_integrable shift sideL edgeL sideR edgeR).const_mul 2)
    (sourceOriginWardBalance_integrable shift sideL edgeL sideR edgeR),integral_const_mul,
    sourceInternalPhaseFormFactor_integral]
  ring

theorem sourceOriginBalance_price (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ‖∫k : Position,sourceOriginWardBalance shift sideL edgeL sideR edgeR k‖≤
      sourceEnergyDiracPrice (fieldDirection (sourceNativeOriginReal 0))/‖sourceChargedRawPacket sideR edgeR‖+
        ‖2*(sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR/(ActionNormalization.phaseMomentum:ℂ))‖ := by
  have equality : (∫k : Position,sourceOriginWardBalance shift sideL edgeL sideR edgeR k)=
      (∫k : Position,sourceFiniteOriginWardIntegrand shift sideL edgeL sideR edgeR k)-
        2*(sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR/(ActionNormalization.phaseMomentum:ℂ)) := by
    simp_rw [sourceOriginWardBalance_generated]
    rw [integral_add ((sourceOriginPhasePair_integrable shift sideL edgeL sideR edgeR).const_mul 2)
      (sourceOriginWardBalance_integrable shift sideL edgeL sideR edgeR),integral_const_mul,sourceOriginPhasePair_return]
    ring
  rw [equality]
  exact (norm_sub_le _ _).trans (add_le_add (sourceFiniteOriginWard_bound shift sideL edgeL sideR edgeR) (le_refl _))

end LowEnergy.PreparationPhysicalInternalOriginPoleAssembly
