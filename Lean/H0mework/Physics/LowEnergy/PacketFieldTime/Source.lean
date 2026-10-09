import H0mework.Physics.LowEnergy.PacketFieldTime.Compact
import H0mework.Physics.LowEnergy.PacketField.Retarded

/-! The original current supplies a C1 branch in the whole compact-band
Banach space, before any merely Borel pole coefficient is multiplied. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
open FullQuantum FullSpace PacketPairResponse PacketField PacketFourier LightCausal DrivenInteraction
noncomputable section
attribute [local irreducible] phasePacket

def branchFamily (energy damping : ℝ) (positive : 0<damping) (sign : Bool)
    (point : LightBand) (time : ℝ) : FullMatterL2 :=
  branchOnBand energy damping positive sign time point

theorem branchFamily_continuous (energy damping : ℝ) (positive : 0<damping) (sign : Bool) :
    Continuous (branchFamily energy damping positive sign).uncurry := by
  have identity : branchFamily energy damping positive sign=
      fun point time => time • bandSlope energy damping positive true sign point time := by
    funext point time
    exact phaseBranch_slope energy damping positive true sign point time
  rw [identity]
  exact continuous_snd.smul (bandSlope_continuous energy damping positive true sign)

def branchVelocity (energy damping : ℝ) (positive : 0<damping) (sign : Bool)
    (point : LightBand) (time : ℝ) : FullMatterL2 :=
  (growthSign sign*(thetaRate (bandMomentum point) : ℂ)) • branchFamily energy damping positive sign point time+
    bandCurrent energy damping positive true point time

theorem branchVelocity_continuous (energy damping : ℝ) (positive : 0<damping) (sign : Bool) :
    Continuous (branchVelocity energy damping positive sign).uncurry := by
  have rate : Continuous (fun pair : LightBand×ℝ => growthSign sign*(thetaRate (bandMomentum pair.1) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (bandRate_continuous.comp continuous_fst))
  exact (rate.smul (branchFamily_continuous energy damping positive sign)).add
    (bandCurrent_continuous energy damping positive true)

theorem branchFamily_derivative (energy damping : ℝ) (positive : 0<damping) (sign : Bool)
    (point : LightBand) (time : ℝ) :
    HasDerivAt (branchFamily energy damping positive sign point)
      (branchVelocity energy damping positive sign point time) time := by
  have actual := phaseBranch_derivative energy damping positive (bandShift point) sign time
  rw [bandShift_physical] at actual
  exact actual

def branchCurve (energy damping : ℝ) (positive : 0<damping) (sign : Bool) (time : ℝ) : C(LightBand,FullMatterL2) :=
  compactSection (branchFamily energy damping positive sign) (branchFamily_continuous energy damping positive sign) time

def branchSpeed (energy damping : ℝ) (positive : 0<damping) (sign : Bool) (time : ℝ) : C(LightBand,FullMatterL2) :=
  compactSection (branchVelocity energy damping positive sign) (branchVelocity_continuous energy damping positive sign) time

theorem branchCurve_derivative (energy damping : ℝ) (positive : 0<damping) (sign : Bool) (time : ℝ) :
    HasDerivAt (branchCurve energy damping positive sign) (branchSpeed energy damping positive sign time) time :=
  compactSection_derivative _ _ (branchFamily_continuous energy damping positive sign)
    (branchVelocity_continuous energy damping positive sign) (branchFamily_derivative energy damping positive sign) time

theorem branchSpeed_continuous (energy damping : ℝ) (positive : 0<damping) (sign : Bool) :
    Continuous (branchSpeed energy damping positive sign) :=
  compactSection_continuous _ (branchVelocity_continuous energy damping positive sign)

theorem branchCurve_initial (energy damping : ℝ) (positive : 0<damping) (sign : Bool) :
    branchCurve energy damping positive sign 0=0 := by
  apply ContinuousMap.ext
  intro point
  exact phaseBranch_initial energy damping positive (bandShift point) sign

theorem branchSpeed_initial (energy damping : ℝ) (positive : 0<damping) (sign : Bool) (point : LightBand) :
    branchSpeed energy damping positive sign 0 point=phasePacket energy damping positive (bandShift point) 0 := by
  simp only [branchSpeed,compactSection,branchVelocity,branchFamily,branchOnBand,
    phaseBranch_initial,smul_zero,zero_add,bandCurrent,orientedShift,ite_true]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
