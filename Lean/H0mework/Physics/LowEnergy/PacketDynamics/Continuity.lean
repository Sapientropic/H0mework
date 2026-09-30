import H0mework.Physics.LowEnergy.PacketDynamics.Flow
import H0mework.Physics.LowEnergy.PacketDynamics.AdjointFlow

/-! Actual locally bounded strong histories act continuously on moving wave packets; operator-norm continuity is not assumed. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace Filter Topology
noncomputable section

theorem strong_apply_continuous {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (family : X → E →L[ℂ] E) (bound : X → ℝ)
    (continuousBound : Continuous bound) (estimate : ∀ x, ‖family x‖ ≤ bound x)
    (strong : ∀ field, Continuous (fun x => family x field))
    (curve : X → E) (continuousCurve : Continuous curve) :
    Continuous (fun x => family x (curve x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have first : Tendsto (fun y => bound y*‖curve y-curve x‖) (𝓝 x) (𝓝 0) := by
    simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
      (continuousBound.tendsto x).mul
        ((continuousCurve.sub (continuous_const (y := curve x))).norm.tendsto x)
  have second : Tendsto (fun y => ‖family y (curve x)-family x (curve x)‖) (𝓝 x) (𝓝 0) := by
    simpa only [Pi.sub_apply,sub_self,norm_zero] using
      (((strong (curve x)).sub (continuous_const (y := family x (curve x)))).norm.tendsto x)
  apply squeeze_zero (fun y => norm_nonneg _) ?_ (by simpa only [zero_add] using first.add second)
  intro y
  have difference : family y (curve y)-family x (curve x)=
      family y (curve y-curve x)+(family y (curve x)-family x (curve x)) := by rw [map_sub]; abel
  rw [difference]
  exact (norm_add_le _ _).trans (add_le_add
    (((family y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (estimate y) (norm_nonneg _))) le_rfl)

theorem spatialFlow_apply_continuous (curve : ℝ → FullMatterL2) (continuousCurve : Continuous curve) :
    Continuous (fun time => spatialFlow 0 time (curve time)) :=
  strong_apply_continuous (spatialFlow 0) (fun time => 1+|time| * sourceRate 0)
    (by fun_prop) (spatialFlow_norm 0) (spatialFlow_stronglyContinuous 0) curve continuousCurve

theorem adjointFlow_norm (time : ℝ) : ‖adjointFlow time‖ ≤ 1+|time| * sourceRate 0 := by
  rw [adjointFlow_original,ContinuousLinearMap.adjoint.norm_map]
  exact spatialFlow_norm 0 time

theorem adjointFlow_apply_continuous (curve : ℝ → FullMatterL2) (continuousCurve : Continuous curve) :
    Continuous (fun time => adjointFlow time (curve time)) :=
  strong_apply_continuous adjointFlow (fun time => 1+|time| * sourceRate 0)
    (by fun_prop) adjointFlow_norm adjointFlow_stronglyContinuous curve continuousCurve

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
