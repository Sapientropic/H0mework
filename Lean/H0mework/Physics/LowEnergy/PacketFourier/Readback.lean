import H0mework.Physics.LowEnergy.PacketFourier.Continuity

/-! Complex Fourier currents are centered in the same source state; their ordered quadratic forms return before any momentum selection. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics HistoryPrepared Stage9DEF
noncomputable section

def phaseMean (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : ℂ :=
  inner ℂ (filteredPacket energy damping positive)
    (phaseCurrentFilter energy damping positive shift time preparedPacket)

def phaseCenteredFilter (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  phaseCurrentFilter energy damping positive shift time-
    phaseMean energy damping positive shift time • sourceFilter energy damping positive

def phasePacket (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : FullMatterL2 :=
  phaseCenteredFilter energy damping positive shift time preparedPacket

def phaseCovariance (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) : ℂ :=
  inner ℂ (phasePacket energy damping positive leftShift leftTime)
    (phasePacket energy damping positive rightShift rightTime)

def phaseCovarianceObservable (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (phaseCenteredFilter energy damping positive leftShift leftTime).adjoint.comp
    (phaseCenteredFilter energy damping positive rightShift rightTime)

theorem phaseCovariance_source_read (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftTime rightTime : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother
        (phaseCovarianceObservable energy damping positive leftShift rightShift leftTime rightTime)))=
      phaseCovariance energy damping positive leftShift rightShift leftTime rightTime := by
  rw [sourceMother_read]
  change inner ℂ preparedPacket ((phaseCenteredFilter energy damping positive leftShift leftTime).adjoint
    (phaseCenteredFilter energy damping positive rightShift rightTime preparedPacket))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

def phaseNoise (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : ℝ :=
  ‖phasePacket energy damping positive shift time‖^2

theorem phaseNoise_read (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    phaseCovariance energy damping positive shift shift time time=(phaseNoise energy damping positive shift time : ℂ) := by
  rw [phaseCovariance,inner_self_eq_norm_sq_to_K]
  simp only [phaseNoise,Complex.ofReal_pow]
  rfl

theorem phaseMean_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (fun pair : Position×ℝ => phaseMean energy damping positive pair.1 pair.2) :=
  continuous_const.inner (phaseCurrentFilter_continuous energy damping positive preparedPacket)

theorem phasePacket_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (fun pair : Position×ℝ => phasePacket energy damping positive pair.1 pair.2) := by
  change Continuous (fun pair : Position×ℝ => phaseCurrentFilter energy damping positive pair.1 pair.2 preparedPacket-
    phaseMean energy damping positive pair.1 pair.2 • filteredPacket energy damping positive)
  exact (phaseCurrentFilter_continuous energy damping positive preparedPacket).sub
    ((phaseMean_continuous energy damping positive).smul continuous_const)

theorem phaseNoise_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (fun pair : Position×ℝ => phaseNoise energy damping positive pair.1 pair.2) :=
  ((phasePacket_continuous energy damping positive).norm).pow 2

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
