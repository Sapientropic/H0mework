import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceLockedDiracTorque

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredLockedChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace FullQuantum.PerturbedGreen
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumPhysicalQuantumLockedCharge
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

/-- The actual preparation order generates a bounded commutator; no zero-torque or charge-value premise is supplied. -/
def sourceLockedFilterTorque : SpatialOperators :=
  sourceLockedSpatialCharge*sourcePacketDiracFilter-sourcePacketDiracFilter*sourceLockedSpatialCharge

def sourceFilteredLockedCorrection (side edge : Fin 2) : FullMatterL2 :=
  ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) • sourceLockedFilterTorque (sourceChargedSpatialPacket side edge)

theorem sourceFilteredLockedAction (side edge : Fin 2) :
    sourceLockedSpatialCharge (sourceChargedFilteredPacket side edge)=
      -(sourceChargedPolarity edge:ℂ) • sourceChargedFilteredPacket side edge+
        sourceFilteredLockedCorrection side edge := by
  change sourceLockedSpatialCharge (((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
    sourcePacketDiracFilter (sourceChargedSpatialPacket side edge))=_
  simp only [map_smul,sourceFilteredLockedCorrection,sourceLockedFilterTorque,sub_apply,mul_apply_eq_comp,
    sourceLockedSpatialPacket,map_smul,smul_sub]
  change _=-(sourceChargedPolarity edge:ℂ) •
    (((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) • sourcePacketDiracFilter (sourceChargedSpatialPacket side edge))+_
  rw [smul_comm (-(sourceChargedPolarity edge:ℂ))]
  abel

private theorem filtered_fourier (side edge : Fin 2) :
    fourier (sourceChargedFilteredPacket side edge)=ᵐ[volume]
      fun k=>((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
        Retarded.diracValue 0 (physicalMomentum k) 0 1 (fourier (sourceChargedSpatialPacket side edge) k) := by
  have identity : sourceChargedFilteredPacket side edge=
      ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) • sourceChargedRawPacket side edge:=rfl
  rw [identity,map_smul]
  filter_upwards [Lp.coeFn_smul ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ)
    (fourier (sourceChargedRawPacket side edge)),
    SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge)] with k scaled green
  rw [scaled]
  change ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
    fourier (SpatialGreen.green 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge)) k=_
  rw [green]

/-- The correction is the full original Dirac torque, not a norm bound or a fitted remainder. -/
theorem sourceFilteredLockedCorrection_fourier (side edge : Fin 2) :
    fourier (sourceFilteredLockedCorrection side edge)=ᵐ[volume]
      fun k=>Retarded.diracValue 0 (physicalMomentum k) 0 1
        (sourceLockedDiracTorque (physicalMomentum k) (fourier (sourceChargedFilteredPacket side edge) k)) := by
  have relation:=congrArg FullSpace.fourier (sourceFilteredLockedAction side edge)
  rw [sourceLockedSpatialCharge,GaugeGreen.constant_fourier,map_add,map_smul] at relation
  have chargeRead:=sourceLockedFiberCharge.coeFn_compLpL (fourier (sourceChargedFilteredPacket side edge))
  rw [relation] at chargeRead
  filter_upwards [chargeRead,Lp.coeFn_add
      (-(sourceChargedPolarity edge:ℂ) • fourier (sourceChargedFilteredPacket side edge))
      (fourier (sourceFilteredLockedCorrection side edge)),
    Lp.coeFn_smul (-(sourceChargedPolarity edge:ℂ)) (fourier (sourceChargedFilteredPacket side edge)),
    filtered_fourier side edge,sourceLockedPacket_fourier side edge] with k read added scaled green initial
  rw [added] at read
  simp only [Pi.add_apply] at read
  rw [scaled] at read
  simp only [Pi.smul_apply] at read
  have commutator:=DFunLike.congr_fun (sourceLockedGreen_commutator (physicalMomentum k))
    (fourier (sourceChargedSpatialPacket side edge) k)
  simp only [mul_apply_eq_comp,add_apply] at commutator
  rw [initial,map_smul] at commutator
  have normalized : sourceLockedFiberCharge (fourier (sourceChargedFilteredPacket side edge) k)=
      -(sourceChargedPolarity edge:ℂ) • fourier (sourceChargedFilteredPacket side edge) k+
        Retarded.diracValue 0 (physicalMomentum k) 0 1
          (sourceLockedDiracTorque (physicalMomentum k) (fourier (sourceChargedFilteredPacket side edge) k)) := by
    rw [green]
    simp only [map_smul]
    rw [commutator,smul_add]
    module
  exact add_left_cancel (read.trans normalized)

def sourceFilteredLockedCurrent (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  (ActionNormalization.phaseMomentum:ℂ)*sourceChargedQuantumRead sideL edgeL sideR edgeR sourceLockedSpatialCharge

/-- Both actual preparation legs read the retained source torque. -/
theorem sourceFilteredLockedCurrent_generated (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredLockedCurrent sideL edgeL sideR edgeR=
      -(ActionNormalization.phaseMomentum:ℂ)*(sourceChargedPolarity edgeR:ℂ)*
        inner ℂ (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR)+
      (ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket sideL edgeL)
        (sourceFilteredLockedCorrection sideR edgeR) := by
  rw [sourceFilteredLockedCurrent,sourceChargedQuantumRead_generated,sourceFilteredLockedAction,
    inner_add_right,inner_smul_right]
  ring

theorem sourceFilteredLockedTorque_integrable (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (fun k : Position=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
      (Retarded.diracValue 0 (physicalMomentum k) 0 1
        (sourceLockedDiracTorque (physicalMomentum k) (fourier (sourceChargedFilteredPacket sideR edgeR) k)))) := by
  apply (L2.integrable_inner (𝕜:=ℂ) (fourier (sourceChargedFilteredPacket sideL edgeL))
    (fourier (sourceFilteredLockedCorrection sideR edgeR))).congr
  filter_upwards [sourceFilteredLockedCorrection_fourier sideR edgeR] with k correction
  rw [correction]

theorem sourceFilteredLockedCurrent_fourier (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredLockedCurrent sideL edgeL sideR edgeR=
      -(ActionNormalization.phaseMomentum:ℂ)*(sourceChargedPolarity edgeR:ℂ)*
        inner ℂ (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR)+
      (ActionNormalization.phaseMomentum:ℂ)*(∫k : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
        (Retarded.diracValue 0 (physicalMomentum k) 0 1
          (sourceLockedDiracTorque (physicalMomentum k) (fourier (sourceChargedFilteredPacket sideR edgeR) k)))) := by
  have pair : inner ℂ (sourceChargedFilteredPacket sideL edgeL) (sourceFilteredLockedCorrection sideR edgeR)=
      ∫k : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
        (Retarded.diracValue 0 (physicalMomentum k) 0 1
          (sourceLockedDiracTorque (physicalMomentum k) (fourier (sourceChargedFilteredPacket sideR edgeR) k))) := by
    rw [←fourier.inner_map_map,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [sourceFilteredLockedCorrection_fourier sideR edgeR] with k correction
    rw [correction]
  rw [sourceFilteredLockedCurrent_generated,pair]

end LowEnergy.PreparationPhysicalFilteredLockedChargeReturn
