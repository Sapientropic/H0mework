import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceInternalOriginAssembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstTemporalWeightedCharge

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredFirstPhaseReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace YangMills.FullPairing CanonicalGradedSpatialSource
open Stage10.CanonicalMatter FullQuantum.Triangular
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePhaseChargeInventory
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedScatteringPoleReturn
open PreparationPhysicalInternalChargePoleReturn PreparationPhysicalFiniteTransferOriginWard
open PreparationPhysicalInternalOriginPoleAssembly
open Filter MeasureTheory
open scoped BigOperators Matrix InnerProductSpace Topology

/-- The complete source difference is retained on the full mother carrier. -/
def sourceFirstPhaseDifference : YangMills.FullPairing.Mother := sourceFirstTemporalCharge-phaseInverse.comp sourcePhaseNoether

theorem sourceFirstPhaseDifference_generated :
    sourceFirstPhaseDifference=(-Complex.I) • (sourceFirstTemporalDifference+sourcePhaseGaugeDifference) := by
  rw [sourceFirstPhaseDifference,sourceFirstTemporalCharge_phase,sourcePhaseNoether_canonical]
  module

theorem sourceFirstPhaseDifference_embed (values : Stage9DEF.Source.Index→ℂ) :
    sourceFirstPhaseDifference (Stage9DEF.Compatibility.embed values)=0 := by
  rw [sourceFirstPhaseDifference_generated]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,sourceFirstTemporalDifference_embed,
    sourcePhaseGaugeDifference_embed,zero_add,smul_zero]

def sourceFirstPhaseDifferenceFiber : FiberOperators := operator sourceFirstPhaseDifference

theorem sourceFirstPhaseDifference_carrier (values : Stage9DEF.Source.Index→ℂ) :
    sourceFirstPhaseDifferenceFiber (naturalCoordinates (Stage9DEF.Compatibility.embed values))=0 := by
  rw [sourceFirstPhaseDifferenceFiber,operator_coordinates,sourceFirstPhaseDifference_embed,map_zero]

attribute [local irreducible] sourceFirstPhaseDifference sourceFirstPhaseDifferenceFiber
  sourceChargedFilteredPacket sourceOriginPhaseFiber

/-- This consumes every moving pole of the actual filter, including its own principal inverse and normalization. -/
theorem sourceFirstPhaseDifference_fourier (side edge : Fin 2) :
    (fun k : Position=>sourceFirstPhaseDifferenceFiber (fourier (sourceChargedFilteredPacket side edge) k))=ᵐ[volume]
      fun _=>0 := by
  filter_upwards [sourceActualFilteredPacket_poles side edge] with k poles
  rw [poles]
  simp only [map_sum,map_smul,sourceFirstPhaseDifference_carrier,smul_zero,Finset.sum_const_zero]

theorem sourceFirstPhaseDifference_shifted (shift : Position) (side edge : Fin 2) :
    sourceFirstPhaseDifferenceFiber.compLpL 2 volume
      (PacketNoise.phaseShift shift (sourceChargedFilteredPacket side edge))=0 := by
  apply fourier.injective
  rw [map_zero,GaugeGreen.constant_fourier,PacketNoise.phaseShift_fourier]
  apply Lp.ext
  have moved:=(measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (sourceFirstPhaseDifference_fourier side edge)
  filter_upwards [sourceFirstPhaseDifferenceFiber.coeFn_compLpL
    (PacketNoise.frequencyShift shift (fourier (sourceChargedFilteredPacket side edge))),
    PacketNoise.frequencyShift_ae shift (fourier (sourceChargedFilteredPacket side edge)),moved,
    (show ⇑(0:FullMatterL2)=ᵐ[volume] (fun _=>0) from Lp.coeFn_zero _ 2 volume)] with k reader shifted zero zeroRead
  rw [reader,shifted,zero,zeroRead]

theorem sourceFirstPhaseDifference_filtered (side edge : Fin 2) :
    sourceFirstPhaseDifferenceFiber.compLpL 2 volume (sourceChargedFilteredPacket side edge)=0 := by
  simpa only [PacketNoise.phaseShift_zero] using sourceFirstPhaseDifference_shifted 0 side edge

private theorem fiber_difference :
    operator sourceFirstTemporalCharge=sourceOriginPhaseFiber+sourceFirstPhaseDifferenceFiber := by
  have source : sourceFirstTemporalCharge=phaseInverse.comp sourcePhaseNoether+sourceFirstPhaseDifference := by
    unfold sourceFirstPhaseDifference
    abel
  rw [source,operator_add]
  unfold sourceOriginPhaseFiber sourceFirstPhaseDifferenceFiber
  rfl

/-- Full-mother differences vanish only after the original shifted filtered ket is supplied. -/
theorem sourceFirstTemporal_filtered (shift : Position) (side edge : Fin 2) :
    (operator sourceFirstTemporalCharge).compLpL 2 volume
      (PacketNoise.phaseShift shift (sourceChargedFilteredPacket side edge))=
      sourceInternalPhaseSpatial (PacketNoise.phaseShift shift (sourceChargedFilteredPacket side edge)) := by
  rw [fiber_difference,ContinuousLinearMap.add_compLpL,add_apply,sourceFirstPhaseDifference_shifted,add_zero]
  unfold sourceInternalPhaseSpatial sourceOriginPhaseFiber
  rfl

end LowEnergy.PreparationPhysicalFilteredFirstPhaseReturn
