import H0mework.Physics.LowEnergy.PacketPairResponse.Band
import H0mework.Physics.LowEnergy.PacketPairResponse.Average

/-! Actual Fourier branch slopes are jointly continuous on the entire source light band and through initial time. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace PacketFourier PacketNoise LightCausal DrivenInteraction
noncomputable section
attribute [local irreducible] phasePacket

def orientedShift (orientation : Bool) (point : LightBand) : Position :=
  if orientation then bandShift point else -(bandShift point)

theorem orientedShift_continuous (orientation : Bool) : Continuous (orientedShift orientation) := by
  cases orientation
  · exact bandShift_continuous.neg
  · exact bandShift_continuous

theorem orientedShift_rate (orientation : Bool) (point : LightBand) :
    thetaRate (physicalMomentum (orientedShift orientation point))=thetaRate (bandMomentum point) := by
  cases orientation
  · exact (thetaRate_opposite (bandShift point)).trans (congrArg thetaRate (bandShift_physical point))
  · exact congrArg thetaRate (bandShift_physical point)

def bandCurrent (energy damping : ℝ) (positive : 0 < damping) (orientation : Bool) (point : LightBand) (time : ℝ) :
    FullMatterL2 := phasePacket energy damping positive (orientedShift orientation point) time

theorem bandCurrent_continuous (energy damping : ℝ) (positive : 0 < damping) (orientation : Bool) :
    Continuous (bandCurrent energy damping positive orientation).uncurry :=
  (phasePacket_continuous energy damping positive).comp
    (((orientedShift_continuous orientation).comp continuous_fst).prodMk continuous_snd)

def bandSlope (energy damping : ℝ) (positive : 0 < damping) (orientation sign : Bool)
    (point : LightBand) (time : ℝ) : FullMatterL2 :=
  responseAverage (growthSign sign*(thetaRate (bandMomentum point) : ℂ))
    (bandCurrent energy damping positive orientation point) time

theorem bandSlope_continuous (energy damping : ℝ) (positive : 0 < damping) (orientation sign : Bool) :
    Continuous (fun pair : LightBand×ℝ => bandSlope energy damping positive orientation sign pair.1 pair.2) :=
  responseAverage_continuous _
    (continuous_const.mul (Complex.continuous_ofReal.comp bandRate_continuous))
    _ (bandCurrent_continuous energy damping positive orientation)

theorem phaseBranch_slope (energy damping : ℝ) (positive : 0 < damping) (orientation sign : Bool)
    (point : LightBand) (time : ℝ) :
    phaseBranch energy damping positive (orientedShift orientation point) time sign=
      time • bandSlope energy damping positive orientation sign point time := by
  rw [phaseBranch,orientedShift_rate,forcedVector_average]
  rfl

theorem bandSlope_initial (energy damping : ℝ) (positive : 0 < damping) (orientation sign : Bool) (point : LightBand) :
    bandSlope energy damping positive orientation sign point 0=
      phasePacket energy damping positive (orientedShift orientation point) 0 :=
  responseAverage_initial _ _

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
