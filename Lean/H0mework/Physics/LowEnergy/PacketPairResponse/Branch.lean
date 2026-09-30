import H0mework.Physics.LowEnergy.PacketFourier.Native
import H0mework.Physics.LowEnergy.PacketFeedback.Leading
import H0mework.Physics.LowEnergy.DrivenInteraction.Response

/-! Opposite Fourier currents feed the actual causal growth branches on the same fixed source preparation. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace PacketNoise PacketDynamics PacketFourier LightCausal LightSpace DrivenInteraction
noncomputable section
attribute [local irreducible] phasePacket

theorem radial_opposite (momentum : Fin 3 → ℝ) : radialMomentum (-momentum)=radialMomentum momentum := by
  simp only [radialMomentum,Rotation.momentumRadius,Pi.neg_apply,neg_sq]

theorem physicalMomentum_opposite (shift : Position) : physicalMomentum (-shift)= -(physicalMomentum shift) := by
  funext j
  simp [physicalMomentum,mul_neg]

theorem thetaRate_opposite (shift : Position) : thetaRate (physicalMomentum (-shift))=thetaRate (physicalMomentum shift) := by
  rw [physicalMomentum_opposite]
  simp only [thetaRate,radial_opposite]

def phaseBranch (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) (sign : Bool) : FullMatterL2 :=
  forcedVector (growthSign sign*(thetaRate (physicalMomentum shift) : ℂ))
    (phasePacket energy damping positive shift) time

theorem phasePacket_time_continuous (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    Continuous (phasePacket energy damping positive shift) := by
  have path : Continuous (fun time : ℝ => (shift,time)) := continuous_const.prodMk continuous_id
  exact (phasePacket_continuous energy damping positive).comp path

theorem phaseBranch_initial (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (sign : Bool) :
    phaseBranch energy damping positive shift 0 sign=0 := forcedVector_initial _ _

theorem phaseBranch_derivative (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (sign : Bool) (time : ℝ) :
    HasDerivAt (fun t => phaseBranch energy damping positive shift t sign)
      ((growthSign sign*(thetaRate (physicalMomentum shift) : ℂ)) • phaseBranch energy damping positive shift time sign+
        phasePacket energy damping positive shift time) time :=
  forcedVector_derivative _ _ (phasePacket_time_continuous energy damping positive shift) time

theorem phaseBranch_initial_derivative (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (sign : Bool) :
    HasDerivAt (fun time => phaseBranch energy damping positive shift time sign)
      (phasePacket energy damping positive shift 0) 0 := by
  have actual := phaseBranch_derivative energy damping positive shift sign 0
  rw [phaseBranch_initial,smul_zero,zero_add] at actual
  exact actual

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
