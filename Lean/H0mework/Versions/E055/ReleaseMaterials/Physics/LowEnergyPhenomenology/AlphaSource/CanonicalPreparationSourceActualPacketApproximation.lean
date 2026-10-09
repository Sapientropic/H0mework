import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceUniformSpatialResponse
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.CanonicalPacket
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualSpatialPacket
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace HistoryPrepared Electromagnetic
open PreparationVacuumStaticSpatialSource CanonicalGradedSpatialSource
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace SchwartzMap FourierTransform
local instance (p : Prop) : Decidable p:=Classical.propDecidable p

abbrev PacketL2 := Lp (α:=FullSpace.Position) ℂ 2 volume

/-- Scalar envelope of the existing HistoryPrepared packet: the same unit ball and the same packetScale. -/
def sourcePacketShape : PacketL2 :=
  ((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) • indicatorConstLp (μ:=volume) 2
    (measurableSet_ball (x:=(0:FullSpace.Position)) (ε:=1)) measure_ball_ne_top (1:ℂ)

theorem sourcePacketShape_ae : sourcePacketShape=ᵐ[volume]
    fun x : FullSpace.Position=>if x∈Metric.ball 0 1 then ((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) else 0 := by
  filter_upwards [Lp.coeFn_smul ((HistoryPrepared.packetScale⁻¹:ℝ):ℂ)
    (indicatorConstLp (μ:=volume) 2 (measurableSet_ball (x:=(0:FullSpace.Position)) (ε:=1)) measure_ball_ne_top (1:ℂ)),
    indicatorConstLp_coeFn (μ:=volume) (p:=2) (hs:=measurableSet_ball (x:=(0:FullSpace.Position)) (ε:=1))
      (hμs:=measure_ball_ne_top) (c:=(1:ℂ))] with x scaled original
  rw [sourcePacketShape,scaled,Pi.smul_apply,original]
  by_cases inside : x∈Metric.ball (0:FullSpace.Position) 1 <;> simp [inside]

theorem sourcePacketShape_unit : ‖sourcePacketShape‖=1 := by
  rw [sourcePacketShape,norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr HistoryPrepared.packetScale_positive.le),
    norm_indicatorConstLp (by norm_num) (by norm_num)]
  norm_num only [norm_one,one_mul]
  change HistoryPrepared.packetScale⁻¹*HistoryPrepared.packetScale=1
  exact inv_mul_cancel₀ HistoryPrepared.packetScale_positive.ne'

/-- This envelope is read from the original source packet map for every original matter vector. -/
theorem sourcePacketShape_original (v : YangMills.FullPairing.Hilbert) :
    HistoryPrepared.preparation v=ᵐ[volume] fun x=>sourcePacketShape x • v := by
  have scalar:=sourcePacketShape_ae
  have original:=indicatorConstLp_coeFn (μ:=volume) (p:=2)
    (hs:=measurableSet_ball (x:=(0:FullSpace.Position)) (ε:=1)) (hμs:=measure_ball_ne_top) (c:=v)
  have scaled:=Lp.coeFn_smul ((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) (HistoryPrepared.packet v)
  filter_upwards [scalar,original,scaled] with x shape packet scale
  change (((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) • HistoryPrepared.packet v) x=_
  rw [scale]
  change ((HistoryPrepared.packetScale⁻¹:ℝ):ℂ) • HistoryPrepared.packet v x=_
  change HistoryPrepared.packet v x=_ at packet
  rw [packet,shape]
  by_cases inside : x∈Metric.ball (0:FullSpace.Position) 1 <;> simp [inside]

theorem sourceCanonicalPacket_shape (momentum : PhysicalMomentum) :
    CanonicalPacket.packet momentum=ᵐ[volume] fun x=>sourcePacketShape x •
      Stage10.ChargedPreparation.CanonicalParticle.state 0 momentum := by
  rw [CanonicalPacket.packet_original]
  exact sourcePacketShape_original _

/-- Frequency envelope obtained by the original unitary spatial Fourier map. -/
def sourceFrequencyPacket : PacketL2 :=
  Lp.fourierTransformₗᵢ FullSpace.Position ℂ sourcePacketShape

theorem sourceFrequencyPacket_unit : ‖sourceFrequencyPacket‖=1 := by
  rw [sourceFrequencyPacket,LinearIsometryEquiv.norm_map]
  exact sourcePacketShape_unit

private theorem source_packet_approx_exists (epsilon : ℝ) (positive : 0<epsilon) :
    ∃f : 𝓢(FullSpace.Position,ℂ),‖f.toLp 2 volume-sourceFrequencyPacket‖<epsilon := by
  have dense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure FullSpace.Position)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  obtain ⟨f,h⟩:=dense.exists_dist_lt sourceFrequencyPacket positive
  refine ⟨f,?_⟩
  simpa only [dist_eq_norm,SchwartzMap.toLpCLM_apply,norm_sub_rev] using h

/-- The original packet produces its own controlled Schwartz approximation; no replacement profile is supplied. -/
def sourcePacketApprox (epsilon : ℝ) (positive : 0<epsilon) : 𝓢(FullSpace.Position,ℂ) :=
  Classical.choose (source_packet_approx_exists epsilon positive)

theorem sourcePacketApprox_error (epsilon : ℝ) (positive : 0<epsilon) :
    ‖(sourcePacketApprox epsilon positive).toLp 2 volume-sourceFrequencyPacket‖<epsilon :=
  Classical.choose_spec (source_packet_approx_exists epsilon positive)

theorem sourcePacketApprox_norm (epsilon : ℝ) (positive : 0<epsilon) :
    ‖(sourcePacketApprox epsilon positive).toLp 2 volume‖≤1+epsilon := by
  have h:=norm_le_norm_add_norm_sub sourceFrequencyPacket ((sourcePacketApprox epsilon positive).toLp 2 volume)
  rw [sourceFrequencyPacket_unit,norm_sub_rev] at h
  linarith [sourcePacketApprox_error epsilon positive]

/-- Two independent approximation accuracies retain the original two scalar legs. -/
def sourcePacketProfile (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) : 𝓢(FullSpace.Position,ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (sourcePacketApprox right rightPositive).hasTemperateGrowth
    (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap (sourcePacketApprox left leftPositive))

theorem sourcePacketProfile_apply (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right)
    (frequency : FullSpace.Position) :
    sourcePacketProfile left right leftPositive rightPositive frequency=
      star (sourcePacketApprox left leftPositive frequency)*sourcePacketApprox right rightPositive frequency := rfl

/-- The original Euclidean/product coordinate equivalence returns the generated profile to the paid spatial reader. -/
def sourcePacketTest (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) : 𝓢(PhysicalMomentum,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3=>ℝ)).symm
      (sourcePacketProfile left right leftPositive rightPositive)

theorem sourcePacketTest_apply (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right)
    (frequency : PhysicalMomentum) :
    sourcePacketTest left right leftPositive rightPositive frequency=
      star (sourcePacketApprox left leftPositive (WithLp.toLp 2 frequency))*
        sourcePacketApprox right rightPositive (WithLp.toLp 2 frequency) := rfl

end LowEnergy.PreparationVacuumActualSpatialPacket
