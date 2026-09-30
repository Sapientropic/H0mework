import H0mework.Physics.LowEnergy.PacketDynamics.CurrentContinuity

/-! The fixed source preparation reads the complete time current and its centered two-time Gram, with no intermediate filtering. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace HistoryPrepared PacketNoise Stage9DEF
noncomputable section

def timeMean (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : ℂ :=
  inner ℂ (filteredPacket energy damping positive)
    (timeCurrentFilter energy damping positive shift time preparedPacket)

def timeMeanObservable (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (sourceFilter energy damping positive).adjoint.comp (timeCurrentFilter energy damping positive shift time)

theorem timeMean_source_read (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (timeMeanObservable energy damping positive shift time)))=
        timeMean energy damping positive shift time := by
  rw [sourceMother_read]
  change inner ℂ preparedPacket ((sourceFilter energy damping positive).adjoint
    (timeCurrentFilter energy damping positive shift time preparedPacket))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

def timeCenteredFilter (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  timeCurrentFilter energy damping positive shift time-
    timeMean energy damping positive shift time • sourceFilter energy damping positive

def timeCovariance (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) : ℂ :=
  inner ℂ (timeCenteredFilter energy damping positive leftShift leftTime preparedPacket)
    (timeCenteredFilter energy damping positive rightShift rightTime preparedPacket)

def timeCovarianceObservable (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (timeCenteredFilter energy damping positive leftShift leftTime).adjoint.comp
    (timeCenteredFilter energy damping positive rightShift rightTime)

theorem timeCovariance_source_read (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother
        (timeCovarianceObservable energy damping positive leftShift rightShift leftTime rightTime)))=
      timeCovariance energy damping positive leftShift rightShift leftTime rightTime := by
  rw [sourceMother_read]
  change inner ℂ preparedPacket ((timeCenteredFilter energy damping positive leftShift leftTime).adjoint
    (timeCenteredFilter energy damping positive rightShift rightTime preparedPacket))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem timeMean_continuous (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    Continuous (timeMean energy damping positive shift) :=
  continuous_const.inner (timeCurrentFilter_continuous energy damping positive shift preparedPacket)

theorem timeCenteredFilter_continuous (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (input : FullMatterL2) :
    Continuous (fun time => timeCenteredFilter energy damping positive shift time input) := by
  change Continuous (fun time => timeCurrentFilter energy damping positive shift time input-
    timeMean energy damping positive shift time • sourceFilter energy damping positive input)
  exact (timeCurrentFilter_continuous energy damping positive shift input).sub
    ((timeMean_continuous energy damping positive shift).smul continuous_const)

theorem timeCovariance_continuous (energy damping : ℝ) (positive : 0 < damping) (leftShift rightShift : Position) :
    Continuous (fun pair : ℝ×ℝ => timeCovariance energy damping positive leftShift rightShift pair.1 pair.2) :=
  ((timeCenteredFilter_continuous energy damping positive leftShift preparedPacket).comp continuous_fst).inner
    ((timeCenteredFilter_continuous energy damping positive rightShift preparedPacket).comp continuous_snd)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
