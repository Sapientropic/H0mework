import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceEnergyDiracLeg
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.PacketNoise.Shift

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedEnergyVariation
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage10 Stage9C.Material.SpinPair
open FullQuantum FullSpace YangMills.FullPairing
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumSourceFieldFamily
open PreparationPhysicalNormalizedFullField PreparationVacuumVoltageGaussGreen
open PreparationVacuumActualFieldQuantization PreparationVacuumElectromagneticIdentity
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

/-- The differentiated field acts before its original plane-wave transfer. -/
def sourceChargedEnergyPreparation (v : ActionState) (shift : Position) (side edge : Fin 2) :
    Hilbert→L[ℂ] FullMatterL2 :=
  ((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) •
    (PacketNoise.phaseShift shift).toContinuousLinearMap.comp
      ((sourceEnergyDiracLeg v).comp (HistoryPrepared.preparation.comp
        (operator (actualRestStatePreparation (sourceChargedRestIndex side edge)))))

theorem sourceChargedEnergyPreparation_applied (v : ActionState) (shift : Position) (side edge : Fin 2) :
    sourceChargedEnergyPreparation v shift side edge (YangMills.FullPairing.prepared 0)=
      PacketNoise.phaseShift shift (sourceChargedEnergyVector v side edge) := by
  simp only [sourceChargedEnergyPreparation,smul_apply,ContinuousLinearMap.comp_apply]
  rw [←sourceChargedSpatialPacket_maker,sourceChargedEnergyVector,map_smul]
  rfl

def sourceChargedEnergyMother (v : ActionState) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    YangMills.FullPairing.Mother :=
  fromOperator ((sourceChargedPreparation sideL edgeL).adjoint.comp
    (sourceChargedEnergyPreparation v shift sideR edgeR))

def sourceChargedEnergyRead (v : ActionState) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Compatibility.responseMatrix (sourceChargedEnergyMother v shift sideL edgeL sideR edgeR))

theorem sourceChargedEnergyRead_generated (v : ActionState) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyRead v shift sideL edgeL sideR edgeR=
      inner ℂ (sourceChargedFilteredPacket sideL edgeL)
        (PacketNoise.phaseShift shift (sourceChargedEnergyVector v sideR edgeR)) := by
  rw [sourceChargedEnergyRead,sourceChargedEnergyMother,origin_response,operator_fromOperator]
  change inner ℂ (YangMills.FullPairing.prepared 0)
    ((sourceChargedPreparation sideL edgeL).adjoint
      (sourceChargedEnergyPreparation v shift sideR edgeR (YangMills.FullPairing.prepared 0)))=_
  rw [ContinuousLinearMap.adjoint_inner_right,sourceChargedPreparation_applied,
    sourceChargedEnergyPreparation_applied]

theorem sourceChargedEnergyRead_norm (v : ActionState) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourceChargedEnergyRead v shift sideL edgeL sideR edgeR‖ ≤
      sourceEnergyDiracPrice v/‖sourceChargedRawPacket sideR edgeR‖ := by
  rw [sourceChargedEnergyRead_generated]
  apply (norm_inner_le_norm _ _).trans
  rw [sourceChargedFilteredPacket_unit,one_mul,PacketNoise.phaseShift_norm]
  exact sourceChargedEnergyVector_norm v sideR edgeR

theorem sourceChargedEnergyShift_fourier (v : ActionState) (shift : Position) (side edge : Fin 2) :
    fourier (PacketNoise.phaseShift shift (sourceChargedEnergyVector v side edge))=ᵐ[volume]
      fun frequency=>sourceEnergyMatrixRead
        (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState v) (physicalMomentum (frequency-shift)))
        (fourier (sourceChargedFilteredPacket side edge) (frequency-shift)) := by
  rw [PacketNoise.phaseShift_fourier]
  have moved:=(measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (sourceChargedEnergyVector_fourier v side edge)
  exact (PacketNoise.frequencyShift_ae shift _).trans moved

theorem sourceChargedEnergyRead_integrable (v : ActionState) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (fun frequency : Position=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceEnergyMatrixRead
        (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState v) (physicalMomentum (frequency-shift)))
        (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))) volume := by
  apply (L2.integrable_inner (𝕜:=ℂ) (fourier (sourceChargedFilteredPacket sideL edgeL))
    (fourier (PacketNoise.phaseShift shift (sourceChargedEnergyVector v sideR edgeR)))).congr
  filter_upwards [sourceChargedEnergyShift_fourier v shift sideR edgeR] with frequency read
  rw [read]

theorem sourceChargedEnergyRead_fourier (v : ActionState) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyRead v shift sideL edgeL sideR edgeR=
      ∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (sourceEnergyMatrixRead
          (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState v) (physicalMomentum (frequency-shift)))
          (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  rw [sourceChargedEnergyRead_generated,←fourier.inner_map_map]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceChargedEnergyShift_fourier v shift sideR edgeR] with frequency read
  rw [read]

end LowEnergy.PreparationPhysicalChargedEnergyVariation
