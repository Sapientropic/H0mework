import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePreparedVoltageReturn
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrentSymbol.Reduction

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageEnergyIdentity
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace
open FullQuantum.FullCurrentSymbol FullQuantum.Triangular ActiveSector
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open StageNineCurrentCoframeMatterTemporalPrincipal
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

/-- This is the existing original twelve-coordinate reducing source image. -/
def sourceVoltageFiberProjection : Hilbert→L[ℂ] Hilbert:=operator ActiveSector.projection

def sourceVoltageSpatialProjection : FullMatterL2→L[ℂ] FullMatterL2:=
  sourceVoltageFiberProjection.compLpL 2 volume

private theorem source_dirac_reducing (p : Fin 3→ℝ) (z : ℂ) :
    Commute ActiveSector.projection (diracKernel actual 0 p z) :=
  ((principal_reducing actual 0).smul_right _).add_right (lower_reducing 0 p)

theorem sourceVoltageDiracGreen_reducing (p : Fin 3→ℝ) :
    Commute sourceVoltageFiberProjection (Retarded.diracValue 0 p 0 1) := by
  let D:=operator (diracKernel actual 0 p (Retarded.spectralParameter 0 1))
  let G:=Retarded.diracValue 0 p 0 1
  have reduced : sourceVoltageFiberProjection*D=D*sourceVoltageFiberProjection := by
    have original:=congrArg operator (source_dirac_reducing p (Retarded.spectralParameter 0 1)).eq
    simpa only [operator_mul,sourceVoltageFiberProjection,D] using original
  have inverse:=Retarded.diracValue_two_sided 0 p 0 1 (by norm_num)
  change D*G=1 ∧ G*D=1 at inverse
  change sourceVoltageFiberProjection*G=G*sourceVoltageFiberProjection
  calc
    _=(G*D)*(sourceVoltageFiberProjection*G):=by rw [inverse.2,one_mul]
    _=G*(D*sourceVoltageFiberProjection)*G:=by noncomm_ring
    _=G*(sourceVoltageFiberProjection*D)*G:=by rw [←reduced]
    _=(G*sourceVoltageFiberProjection)*(D*G):=by noncomm_ring
    _=G*sourceVoltageFiberProjection:=by rw [inverse.1,mul_one]

/-- Full Dirac filtering preserves the original source carrier, including its exact C0 inverse ordering. -/
theorem sourceVoltageSpatialProjection_green (field : FullMatterL2) :
    sourceVoltageSpatialProjection (sourcePacketDiracFilter field)=
      sourcePacketDiracFilter (sourceVoltageSpatialProjection field) := by
  apply fourier.injective
  rw [show fourier (sourceVoltageSpatialProjection (sourcePacketDiracFilter field))=
    sourceVoltageFiberProjection.compLpL 2 volume (fourier (sourcePacketDiracFilter field)) from
      GaugeGreen.constant_fourier sourceVoltageFiberProjection _]
  have projected : fourier (sourceVoltageSpatialProjection field)=
      sourceVoltageFiberProjection.compLpL 2 volume (fourier field):=
    GaugeGreen.constant_fourier sourceVoltageFiberProjection field
  apply Lp.ext
  have right:=SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) (sourceVoltageSpatialProjection field)
  rw [projected] at right
  filter_upwards [sourceVoltageFiberProjection.coeFn_compLpL (fourier (sourcePacketDiracFilter field)),
    SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) field,right,
    sourceVoltageFiberProjection.coeFn_compLpL (fourier field)] with frequency outer original transformed input
  change _=fourier (SpatialGreen.green 0 0 1 (by norm_num) (sourceVoltageSpatialProjection field)) frequency
  rw [outer,transformed,input]
  change sourceVoltageFiberProjection (fourier (SpatialGreen.green 0 0 1 (by norm_num) field) frequency)=_
  rw [original]
  exact DFunLike.congr_fun (sourceVoltageDiracGreen_reducing (physicalMomentum frequency)).eq _

private theorem projection_embed (values : Source.Index→ℂ) :
    ActiveSector.projection (embed values)=embed values := by
  funext spin
  change internalProjection (∑color : Fin 2,values (spin,color) • sourceColorDoubletMatter color)=_
  simp only [map_sum,map_smul,←colorTriplet_original,internalProjection_basis]
  rfl

/-- The actual charged state1/3 preparation, not a replacement source state, lies in that image. -/
theorem sourceChargedRestriction_retained (side edge : Fin 2) :
    sourceVoltageFiberProjection (naturalCoordinates (sourceChargedRestriction side edge))=
      naturalCoordinates (sourceChargedRestriction side edge) := by
  rw [sourceVoltageFiberProjection,operator_coordinates]
  apply congrArg naturalCoordinates
  unfold sourceChargedRestriction
  rw [actualRestState_source]
  exact projection_embed _

private theorem packet_retained (v : Hilbert) (fixed : sourceVoltageFiberProjection v=v) :
    sourceVoltageSpatialProjection (HistoryPrepared.packet v)=HistoryPrepared.packet v := by
  apply Lp.ext
  filter_upwards [sourceVoltageFiberProjection.coeFn_compLpL (HistoryPrepared.packet v),
    indicatorConstLp_coeFn (p:=2) (hs:=measurableSet_ball (x:=(0:Position)) (ε:=1))
      (hμs:=measure_ball_ne_top) (c:=v)] with x projected packetAt
  change sourceVoltageFiberProjection.compLpL 2 volume (HistoryPrepared.packet v) x=_
  rw [projected]
  change sourceVoltageFiberProjection (HistoryPrepared.packet v x)=HistoryPrepared.packet v x
  change HistoryPrepared.packet v x=_ at packetAt
  rw [packetAt]
  by_cases inside : x∈Metric.ball (0:Position) 1
  · simpa only [Set.indicator_of_mem inside,Function.const_apply] using fixed
  · simp only [Set.indicator_of_notMem inside,map_zero]

theorem sourceChargedSpatialPacket_retained (side edge : Fin 2) :
    sourceVoltageSpatialProjection (sourceChargedSpatialPacket side edge)=sourceChargedSpatialPacket side edge := by
  change sourceVoltageSpatialProjection (((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) •
    HistoryPrepared.packet (naturalCoordinates (sourceChargedRestriction side edge)))=_
  rw [map_smul,packet_retained _ (sourceChargedRestriction_retained side edge)]
  rfl

theorem sourceChargedFilteredPacket_retained (side edge : Fin 2) :
    sourceVoltageSpatialProjection (sourceChargedFilteredPacket side edge)=sourceChargedFilteredPacket side edge := by
  change sourceVoltageSpatialProjection (((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
    sourcePacketDiracFilter (sourceChargedSpatialPacket side edge))=_
  rw [map_smul,sourceVoltageSpatialProjection_green,sourceChargedSpatialPacket_retained]
  rfl

end LowEnergy.PreparationPhysicalVoltageEnergyIdentity
