import H0mework.Physics.LowEnergy.PacketDynamics.Readback
import H0mework.Physics.LowEnergy.LightCausal.Convolution

/-! The actual continuum current history drives the original theta pole response on the same Hilbert carrier. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace HistoryPrepared PacketNoise LightCausal
noncomputable section

def packetCurrent (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : FullMatterL2 :=
  timeCenteredFilter energy damping positive shift time preparedPacket

theorem packetCurrent_continuous (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    Continuous (packetCurrent energy damping positive shift) :=
  timeCenteredFilter_continuous energy damping positive shift preparedPacket

def packetPosition (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : FullMatterL2 :=
  metricDevelopment (physicalMomentum shift) (packetCurrent energy damping positive shift) time

def packetVelocity (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : FullMatterL2 :=
  metricVelocity (physicalMomentum shift) (packetCurrent energy damping positive shift) time

theorem packetMotion_initial (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    packetPosition energy damping positive shift 0=0 ∧ packetVelocity energy damping positive shift 0=0 :=
  metricDevelopment_initial _ _

theorem packetPosition_derivative (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    HasDerivAt (packetPosition energy damping positive shift)
      (packetVelocity energy damping positive shift time) time :=
  metricDevelopment_derivative _ _ (packetCurrent_continuous energy damping positive shift) time

theorem packetVelocity_derivative (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    HasDerivAt (packetVelocity energy damping positive shift)
      (((thetaRate (physicalMomentum shift) : ℂ)^2) • packetPosition energy damping positive shift time-
        (2*metricResidue (physicalMomentum shift)*(thetaRate (physicalMomentum shift) : ℂ)) •
          packetCurrent energy damping positive shift time) time :=
  metricVelocity_derivative _ _ (packetCurrent_continuous energy damping positive shift) time

theorem packetPosition_convolution (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    packetPosition energy damping positive shift time=
      ∫ r in (0 : ℝ)..time, futureMetricKernel (physicalMomentum shift) (time-r) •
        packetCurrent energy damping positive shift r :=
  metricDevelopment_convolution _ _ (packetCurrent_continuous energy damping positive shift) time

theorem packetPosition_causal (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) (future : 0 ≤ time) :
    packetPosition energy damping positive shift time=
      ∫ r in (0 : ℝ)..time, metricSourceKernel (physicalMomentum shift) (time-r) •
        packetCurrent energy damping positive shift r :=
  metricDevelopment_causal _ _ (packetCurrent_continuous energy damping positive shift) time future

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
