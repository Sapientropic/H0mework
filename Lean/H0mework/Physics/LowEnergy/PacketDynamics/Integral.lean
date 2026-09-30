import H0mework.Physics.LowEnergy.PacketDynamics.Causal

/-! The induced packet two-point function is the true double time integral of the complete source covariance. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace PacketNoise HistoryPrepared LightCausal Stage9DEF
noncomputable section

def causalIntegrand (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time r : ℝ) : FullMatterL2 :=
  futureMetricKernel (physicalMomentum shift) (time-r) • packetCurrent energy damping positive shift r

theorem causalIntegrand_continuous (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    Continuous (causalIntegrand energy damping positive shift time) := by
  have kernel : Continuous (futureMetricKernel (physicalMomentum shift)) :=
    continuous_iff_continuousAt.mpr (fun r => (futureMetricKernel_derivative _ r).continuousAt)
  exact (kernel.comp (continuous_const.sub continuous_id)).smul (packetCurrent_continuous energy damping positive shift)

theorem interval_inner_right {field : ℝ → FullMatterL2} {first last : ℝ}
    (integrable : IntervalIntegrable field volume first last) (left : FullMatterL2) :
    (∫ r in first..last, inner ℂ left (field r))=inner ℂ left (∫ r in first..last, field r) :=
  (innerSL ℂ left).intervalIntegral_comp_comm integrable

theorem interval_inner_left {field : ℝ → FullMatterL2} {first last : ℝ}
    (integrable : IntervalIntegrable field volume first last) (right : FullMatterL2) :
    (∫ r in first..last, inner ℂ (field r) right)=inner ℂ (∫ r in first..last, field r) right := by
  calc
    _ = ∫ r in first..last, (starRingEnd ℂ) (inner ℂ right (field r)) := by simp only [inner_conj_symm]
    _ = (starRingEnd ℂ) (∫ r in first..last, inner ℂ right (field r)) := intervalIntegral.intervalIntegral_conj
    _ = _ := by
      rw [interval_inner_right integrable]
      exact inner_conj_symm _ _

theorem causalIntegrand_inner (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime left right : ℝ) :
    (starRingEnd ℂ) (futureMetricKernel (physicalMomentum leftShift) (leftTime-left))*
      futureMetricKernel (physicalMomentum rightShift) (rightTime-right)*
        timeCovariance energy damping positive leftShift rightShift left right=
      inner ℂ (causalIntegrand energy damping positive leftShift leftTime left)
        (causalIntegrand energy damping positive rightShift rightTime right) := by
  simp only [causalIntegrand,timeCovariance,packetCurrent,inner_smul_left,inner_smul_right]
  ring

theorem packetPosition_twoPoint (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) :
    (∫ left in (0 : ℝ)..leftTime, ∫ right in (0 : ℝ)..rightTime,
      (starRingEnd ℂ) (futureMetricKernel (physicalMomentum leftShift) (leftTime-left))*
        futureMetricKernel (physicalMomentum rightShift) (rightTime-right)*
          timeCovariance energy damping positive leftShift rightShift left right)=
      inner ℂ (packetPosition energy damping positive leftShift leftTime)
        (packetPosition energy damping positive rightShift rightTime) := by
  have leftIntegrable := (causalIntegrand_continuous energy damping positive leftShift leftTime).intervalIntegrable
    (μ := volume) 0 leftTime
  have rightIntegrable := (causalIntegrand_continuous energy damping positive rightShift rightTime).intervalIntegrable
    (μ := volume) 0 rightTime
  simp_rw [causalIntegrand_inner]
  simp_rw [interval_inner_right rightIntegrable]
  rw [interval_inner_left leftIntegrable,packetPosition_convolution,packetPosition_convolution]
  rfl

theorem packetPosition_source_twoPoint (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) :
    (∫ left in (0 : ℝ)..leftTime, ∫ right in (0 : ℝ)..rightTime,
      (starRingEnd ℂ) (futureMetricKernel (physicalMomentum leftShift) (leftTime-left))*
        futureMetricKernel (physicalMomentum rightShift) (rightTime-right)*
          State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
            (Compatibility.responseMatrix (sourceMother
              (timeCovarianceObservable energy damping positive leftShift rightShift left right))))=
      inner ℂ (packetPosition energy damping positive leftShift leftTime)
        (packetPosition energy damping positive rightShift rightTime) := by
  simp_rw [timeCovariance_source_read]
  exact packetPosition_twoPoint energy damping positive leftShift rightShift leftTime rightTime

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
