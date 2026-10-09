import H0mework.Physics.LowEnergy.PacketPairResponse.Slope
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Jointly continuous source branches and velocities generate a derivative
in the compact-domain Banach space by its actual Bochner integral. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
noncomputable section
variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def compactSection (field : X → ℝ → E) (continuousField : Continuous field.uncurry)
    (time : ℝ) : C(X,E) :=
  ⟨fun point => field point time,continuousField.comp (continuous_id.prodMk continuous_const)⟩

omit [CompleteSpace E] [CompactSpace X] [NormedSpace ℂ E] in
theorem compactSection_continuous (field : X → ℝ → E) (continuousField : Continuous field.uncurry) :
    Continuous (compactSection field continuousField) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuousField.comp continuous_swap

theorem compactSection_integral (field velocity : X → ℝ → E)
    (continuousField : Continuous field.uncurry) (continuousVelocity : Continuous velocity.uncurry)
    (derivative : ∀ point time, HasDerivAt (field point) (velocity point time) time) (time : ℝ) :
    compactSection field continuousField time=compactSection field continuousField 0+
      ∫ t in (0 : ℝ)..time, compactSection velocity continuousVelocity t := by
  apply ContinuousMap.ext
  intro point
  have integrable := (compactSection_continuous velocity continuousVelocity).intervalIntegrable
    (μ := volume) 0 time
  have evaluate := (ContinuousMap.evalCLM ℝ point).intervalIntegral_comp_comm integrable
  change field point time=field point 0+
    (ContinuousMap.evalCLM ℝ point) (∫ t in (0 : ℝ)..time, compactSection velocity continuousVelocity t)
  rw [← evaluate]
  change field point time=field point 0+∫ t in (0 : ℝ)..time, velocity point t
  have regular : Continuous (velocity point) :=
    continuousVelocity.comp (continuous_const.prodMk continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => derivative point t)
    (regular.intervalIntegrable (μ := volume) 0 time)]
  abel

theorem compactSection_derivative (field velocity : X → ℝ → E)
    (continuousField : Continuous field.uncurry) (continuousVelocity : Continuous velocity.uncurry)
    (derivative : ∀ point time, HasDerivAt (field point) (velocity point time) time) (time : ℝ) :
    HasDerivAt (compactSection field continuousField)
      (compactSection velocity continuousVelocity time) time := by
  have regular := compactSection_continuous velocity continuousVelocity
  have integral := intervalIntegral.integral_hasDerivAt_right
    (regular.intervalIntegrable (μ := volume) 0 time)
    regular.aestronglyMeasurable.stronglyMeasurableAtFilter regular.continuousAt
  have generated := integral.const_add (compactSection field continuousField 0)
  have identity : compactSection field continuousField=
      fun time => compactSection field continuousField 0+
        ∫ t in (0 : ℝ)..time, compactSection velocity continuousVelocity t := by
    funext t
    exact compactSection_integral field velocity continuousField continuousVelocity derivative t
  rw [identity]
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
