import H0mework.Physics.LowEnergy.PacketPairResponse.Branch

/-! Each ordered causal-branch Gram is the true double time integral of the
original complete Fourier current covariance on the same Stage10 source. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace PacketFourier PacketDynamics LightCausal DrivenInteraction HistoryPrepared Stage9DEF
noncomputable section
attribute [local irreducible] phasePacket

def phaseKernel (shift : Position) (sign : Bool) (time parameter : ℝ) : ℂ :=
  Complex.exp (growthSign sign*(thetaRate (physicalMomentum shift) : ℂ)*
    ((time-parameter : ℝ) : ℂ))

def phaseIntegrand (energy damping : ℝ) (positive : 0 < damping) (shift : Position)
    (sign : Bool) (time parameter : ℝ) : FullMatterL2 :=
  phaseKernel shift sign time parameter • phasePacket energy damping positive shift parameter

theorem phaseIntegrand_continuous (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (sign : Bool) (time : ℝ) :
    Continuous (phaseIntegrand energy damping positive shift sign time) := by
  have kernel : Continuous (phaseKernel shift sign time) := by unfold phaseKernel; fun_prop
  exact kernel.smul (phasePacket_time_continuous energy damping positive shift)

theorem phaseBranch_convolution (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (sign : Bool) (time : ℝ) :
    phaseBranch energy damping positive shift time sign=
      ∫ parameter in (0 : ℝ)..time, phaseIntegrand energy damping positive shift sign time parameter := by
  rw [phaseBranch,forcedVector_convolution]
  rfl

theorem phaseIntegrand_inner (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftSign rightSign : Bool) (leftTime rightTime left right : ℝ) :
    (starRingEnd ℂ) (phaseKernel leftShift leftSign leftTime left)*phaseKernel rightShift rightSign rightTime right*
      phaseCovariance energy damping positive leftShift rightShift left right=
    inner ℂ (phaseIntegrand energy damping positive leftShift leftSign leftTime left)
      (phaseIntegrand energy damping positive rightShift rightSign rightTime right) := by
  rw [phaseIntegrand,phaseIntegrand,inner_smul_left,inner_smul_right]
  change _=(starRingEnd ℂ) (phaseKernel leftShift leftSign leftTime left)*
    (phaseKernel rightShift rightSign rightTime right*phaseCovariance energy damping positive leftShift rightShift left right)
  ring

theorem phaseBranch_twoPoint (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftSign rightSign : Bool) (leftTime rightTime : ℝ) :
    (∫ left in (0 : ℝ)..leftTime, ∫ right in (0 : ℝ)..rightTime,
      (starRingEnd ℂ) (phaseKernel leftShift leftSign leftTime left)*phaseKernel rightShift rightSign rightTime right*
        phaseCovariance energy damping positive leftShift rightShift left right)=
      inner ℂ (phaseBranch energy damping positive leftShift leftTime leftSign)
        (phaseBranch energy damping positive rightShift rightTime rightSign) := by
  have leftIntegrable := (phaseIntegrand_continuous energy damping positive leftShift leftSign leftTime).intervalIntegrable
    (μ := volume) 0 leftTime
  have rightIntegrable := (phaseIntegrand_continuous energy damping positive rightShift rightSign rightTime).intervalIntegrable
    (μ := volume) 0 rightTime
  simp_rw [phaseIntegrand_inner]
  simp_rw [interval_inner_right rightIntegrable]
  rw [interval_inner_left leftIntegrable,phaseBranch_convolution,phaseBranch_convolution]

theorem phaseBranch_source_twoPoint (energy damping : ℝ) (positive : 0 < damping)
    (leftShift rightShift : Position) (leftSign rightSign : Bool) (leftTime rightTime : ℝ) :
    (∫ left in (0 : ℝ)..leftTime, ∫ right in (0 : ℝ)..rightTime,
      (starRingEnd ℂ) (phaseKernel leftShift leftSign leftTime left)*phaseKernel rightShift rightSign rightTime right*
        State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
          (Compatibility.responseMatrix (sourceMother
            (phaseCovarianceObservable energy damping positive leftShift rightShift left right))))=
      inner ℂ (phaseBranch energy damping positive leftShift leftTime leftSign)
        (phaseBranch energy damping positive rightShift rightTime rightSign) := by
  simp_rw [phaseCovariance_source_read]
  exact phaseBranch_twoPoint energy damping positive leftShift rightShift leftSign rightSign leftTime rightTime

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
