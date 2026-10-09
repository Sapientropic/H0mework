import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageGreenSolution
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceQuantumLockedPoleCharge
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCanonicalPacketDensity

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedPacketVoltage
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open Stage10 Stage10.CanonicalMatter YangMills.FullPairing
open FullQuantum FullSpace HistoryPrepared Electromagnetic
open PreparationVacuumActualSpatialPacket PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open PreparationVacuumVoltageGaussGreen
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace SchwartzMap
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The fixed representative of the original unit-ball packet, with its original normalization. -/
def sourceChargedPacketAmplitude (x : Point) : ℂ :=
  if WithLp.toLp 2 x ∈ Metric.ball (0 : FullSpace.Position) 1
  then ((HistoryPrepared.packetScale⁻¹ : ℝ) : ℂ) else 0

def sourceChargedPacketMatter (side edge : Fin 2) (x : Point) : DiracExteriorMatterCarrier :=
  sourceChargedPacketAmplitude x •
    actualRestStatePreparation (sourceChargedRestIndex side edge) (actual.matter 0)

def sourceChargedPacketDual (side edge : Fin 2) (x : Point) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  star (sourceChargedPacketAmplitude x) •
    (actual.conjugateMatter 0).comp (canonicalDual (actualRestStatePreparation (sourceChargedRestIndex side edge)))

/-- Physical-space preparation of the same internal source vector used by the Gauss creation maker. -/
def sourceChargedSpatialPacket (side edge : Fin 2) : FullMatterL2 :=
  HistoryPrepared.preparation (naturalCoordinates (sourceChargedRestriction side edge))

theorem sourceChargedSpatialPacket_maker (side edge : Fin 2) :
    sourceChargedSpatialPacket side edge=
      HistoryPrepared.preparation (operator (actualRestStatePreparation (sourceChargedRestIndex side edge))
        (YangMills.FullPairing.prepared 0)) := by
  simp only [sourceChargedSpatialPacket,sourceChargedRestriction,YangMills.FullPairing.prepared,
    operator_coordinates]

private theorem amplitude_shape :
    (fun x : Point=>sourcePacketShape (WithLp.toLp 2 x))=ᵐ[volume] sourceChargedPacketAmplitude :=
  (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp sourcePacketShape_ae

theorem sourceChargedSpatialPacket_shape (side edge : Fin 2) :
    (fun x : Point=>sourceChargedSpatialPacket side edge (WithLp.toLp 2 x))=ᵐ[volume]
      fun x=>sourceChargedPacketAmplitude x • naturalCoordinates (sourceChargedRestriction side edge) := by
  have generated := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (sourcePacketShape_original (naturalCoordinates (sourceChargedRestriction side edge)))
  filter_upwards [generated,amplitude_shape] with x packet shape
  simpa only [Function.comp_apply,sourceChargedSpatialPacket,shape] using packet

/-- The raw current is computed from both original material legs, before solving Gauss. -/
theorem sourceChargedPacket_current (side edge : Fin 2) (x : Point) :
    sourceChargedPacketDual side edge x
      (currentAction 0 HyperchargeResponse.chargeDirection (sourceChargedPacketMatter side edge x))=
        -(ActionNormalization.phaseMomentum : ℂ)*(sourcePacketDensity x : ℂ) := by
  simp only [sourceChargedPacketDual,sourceChargedPacketMatter,LinearMap.smul_apply,
    LinearMap.comp_apply,map_smul,smul_eq_mul]
  rw [actualRestState_hypercharge_current]
  by_cases inside : WithLp.toLp 2 x ∈ Metric.ball (0 : FullSpace.Position) 1
  · simp only [sourceChargedPacketAmplitude,if_pos inside,sourcePacketDensity,sourcePacketDensityE,
      indicator_of_mem inside,Complex.star_def,Complex.conj_ofReal]
    push_cast
    ring
  · simp [sourceChargedPacketAmplitude,sourcePacketDensity,sourcePacketDensityE,inside]

theorem sourceChargedPacket_raw (side edge : Fin 2) (x : Point) :
    sourceVoltageRawCharge (sourceChargedPacketMatter side edge) (sourceChargedPacketDual side edge) x=
      -ActionNormalization.phaseMomentum*sourcePacketDensity x := by
  unfold sourceVoltageRawCharge
  rw [sourceChargedPacket_current]
  simp

/-- The spatial reader uses the original phaseInverse density leg of the same preparation. -/
theorem sourceChargedPacket_reader (side edge : Fin 2) :
    (fun x : Point=>sourceChargedPacketDual side edge x
      (currentAction 0 HyperchargeResponse.chargeDirection (sourceChargedPacketMatter side edge x)))=ᵐ[volume]
      fun x=>(4*(spinScale : ℂ))*inner ℂ (sourceChargedSpatialPacket side edge (WithLp.toLp 2 x))
        (CanonicalPacket.densityReader (currentAction 0 HyperchargeResponse.chargeDirection)
          (sourceChargedSpatialPacket side edge (WithLp.toLp 2 x))) := by
  filter_upwards [sourceChargedSpatialPacket_shape side edge] with x packet
  rw [packet,map_smul,inner_smul_left,inner_smul_right]
  have source:=ExternalState.original_prepared_vertex 0
    (actualRestStatePreparation (sourceChargedRestIndex side edge))
    (actualRestStatePreparation (sourceChargedRestIndex side edge))
    (currentAction 0 HyperchargeResponse.chargeDirection)
  simp only [YangMills.FullPairing.prepared,operator_coordinates,LinearMap.comp_apply] at source
  simp only [sourceChargedPacketDual,sourceChargedPacketMatter,LinearMap.smul_apply,
    LinearMap.comp_apply,map_smul,smul_eq_mul]
  rw [source]
  simp only [CanonicalPacket.densityReader,operator_coordinates,LinearMap.comp_apply,
    sourceChargedRestriction,Complex.star_def]
  ring

theorem sourceChargedPacket_integrable (side edge : Fin 2) :
    Integrable (sourceVoltageRawCharge (sourceChargedPacketMatter side edge) (sourceChargedPacketDual side edge)) := by
  apply (sourcePacketDensity_integrable.const_mul (-ActionNormalization.phaseMomentum)).congr
  filter_upwards [] with x
  exact (sourceChargedPacket_raw side edge x).symm

theorem sourceChargedPacket_bounded (side edge : Fin 2) (x : Point) :
    ‖sourceVoltageRawCharge (sourceChargedPacketMatter side edge) (sourceChargedPacketDual side edge) x‖≤
      ‖ActionNormalization.phaseMomentum‖*HistoryPrepared.packetScale⁻¹^2 := by
  rw [sourceChargedPacket_raw,norm_mul,norm_neg]
  exact mul_le_mul_of_nonneg_left (sourcePacketDensity_bounded x) (norm_nonneg _)

theorem sourceChargedPacket_totalCurrent (side edge : Fin 2) :
    (∫x : Point,sourceVoltageRawCharge (sourceChargedPacketMatter side edge) (sourceChargedPacketDual side edge) x)=
      -ActionNormalization.phaseMomentum := by
  simp only [sourceChargedPacket_raw,integral_const_mul,sourcePacketDensity_mass,mul_one]

end LowEnergy.PreparationPhysicalChargedPacketVoltage
