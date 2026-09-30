import H0mework.Physics.LowEnergy.FullQuantum.FullSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

/-! The original full source vector has a normalized spatial packet map, before complete operators are read. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryPrepared
open FullSpace YangMills.FullPairing
noncomputable section

def packet (v : Hilbert) : FullMatterL2 :=
  indicatorConstLp (μ := volume) 2 (measurableSet_ball (x := (0 : Position)) (ε := 1)) measure_ball_ne_top v

def packetScale : ℝ := (volume.real (Metric.ball (0 : Position) 1)) ^ (1 / (2 : ℝ))

theorem packetScale_positive : 0<packetScale := by
  apply Real.rpow_pos_of_pos
  exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume (0 : Position) zero_lt_one)) measure_ball_ne_top

theorem packet_norm (v : Hilbert) : ‖packet v‖=‖v‖ * packetScale := by
  rw [packet,norm_indicatorConstLp (by norm_num) (by norm_num)]
  norm_num [packetScale]

theorem packet_smul (c : ℂ) (v : Hilbert) : packet (c • v)=c • packet v := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball (x := (0 : Position)) (ε := 1))
      (hμs := measure_ball_ne_top) (c := c • v),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball (x := (0 : Position)) (ε := 1))
      (hμs := measure_ball_ne_top) (c := v),Lp.coeFn_smul c (packet v)] with x scaled original output
  rw [output]
  change packet (c • v) x=c • packet v x
  change packet (c • v) x=_ at scaled
  change packet v x=_ at original
  rw [scaled,original]
  by_cases inside : x ∈ Metric.ball (0 : Position) 1
  · simp [inside]
  · simp [inside]

def packetLinear : Hilbert →ₗ[ℂ] FullMatterL2 where
  toFun := packet
  map_add' _ _ := indicatorConstLp_add.symm
  map_smul' c v := packet_smul c v

def packetMap : Hilbert →L[ℂ] FullMatterL2 :=
  packetLinear.mkContinuous packetScale (fun v => (packet_norm v).trans (mul_comm _ _) |>.le)

def preparation : Hilbert →L[ℂ] FullMatterL2 := ((packetScale⁻¹ : ℝ) : ℂ) • packetMap

theorem preparation_norm (v : Hilbert) : ‖preparation v‖=‖v‖ := by
  change ‖((packetScale⁻¹ : ℝ) : ℂ) • packet v‖=‖v‖
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr packetScale_positive.le),packet_norm]
  field_simp [packetScale_positive.ne']

def preparedPacket : FullMatterL2 := preparation (prepared 0)

theorem preparedPacket_unit : ‖preparedPacket‖=1 := (preparation_norm _).trans (prepared_norm 0)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryPrepared
