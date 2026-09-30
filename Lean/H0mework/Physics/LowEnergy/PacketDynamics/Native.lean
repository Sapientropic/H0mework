import H0mework.Physics.LowEnergy.PacketDynamics.Original
import H0mework.Physics.LowEnergy.PacketDynamics.Integral

/-! The original prepared source, complete time current and actual causal response meet at one concrete consumer. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace PacketNoise HistoryPrepared LightCausal
noncomputable section

theorem packetCurrent_original (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    packetCurrent energy damping positive shift time=
      timeCurrentField shift time (preparedDomain energy damping positive)-
        timeCurrentMean shift time (preparedDomain energy damping positive) • filteredPacket energy damping positive := by
  change timeCurrentFilter energy damping positive shift time preparedPacket-
    timeMean energy damping positive shift time • filteredPacket energy damping positive=_
  rw [timeCurrentFilter_prepared,timeMean,timeCurrentFilter_prepared]
  rfl

theorem packetCurrent_initial (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    packetCurrent energy damping positive shift 0=centeredFilter energy damping positive shift preparedPacket := by
  rw [packetCurrent,timeCenteredFilter_zero]

theorem packetCurrent_orthogonal (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    inner ℂ (filteredPacket energy damping positive) (packetCurrent energy damping positive shift time)=0 := by
  have unit : inner ℂ (filteredPacket energy damping positive) (filteredPacket energy damping positive)=1 :=
    inner_self_eq_one_of_norm_eq_one (filteredPacket_unit energy damping positive)
  change inner ℂ (filteredPacket energy damping positive)
    (timeCurrentFilter energy damping positive shift time preparedPacket-
      timeMean energy damping positive shift time • filteredPacket energy damping positive)=0
  rw [inner_sub_right,inner_smul_right,unit,mul_one]
  exact sub_self _

theorem packetPosition_original_convolution (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    packetPosition energy damping positive shift time=
      ∫ r in (0 : ℝ)..time, futureMetricKernel (physicalMomentum shift) (time-r) •
        (timeCurrentField shift r (preparedDomain energy damping positive)-
          timeCurrentMean shift r (preparedDomain energy damping positive) • filteredPacket energy damping positive) := by
  rw [packetPosition_convolution]
  simp_rw [packetCurrent_original]

theorem timeCovariance_initial (energy damping : ℝ) (positive : 0 < damping) (left right : Position) :
    timeCovariance energy damping positive left right 0 0=packetCovariance energy damping positive left right := by
  rw [timeCovariance,timeCenteredFilter_zero,timeCenteredFilter_zero]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
