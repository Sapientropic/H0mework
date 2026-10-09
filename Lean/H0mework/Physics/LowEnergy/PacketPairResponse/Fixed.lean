import H0mework.Physics.LowEnergy.PacketPairResponse.Slope
import H0mework.Physics.LowEnergy.PacketPairResponse.Leading

/-! The fixed laboratory probe consumes the actual source tensor, two spatial
orientations and all four ordered time-growth branches. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace PacketFourier VertexTensor
noncomputable section
attribute [local irreducible] phasePacket bandSlope

def bandCoupling (same : Bool) (point : LightBand) : ℝ :=
  fixedMomentumCoupling same (bandMomentum point)

def fixedFeedback (energy damping : ℝ) (positive : 0 < damping) (point : LightBand) (time : ℝ) : ℝ :=
  oppositeFeedback (bandCoupling true point) (bandCoupling false point)
    energy damping positive (bandShift point) time

def slopeFeedback (energy damping : ℝ) (positive : 0 < damping) (point : LightBand) (time : ℝ) : ℝ :=
  (fourGram (bandCoupling true point) (bandCoupling false point)
      (fun sign => bandSlope energy damping positive true sign point time)+
    fourGram (bandCoupling true point) (bandCoupling false point)
      (fun sign => bandSlope energy damping positive false sign point time))/2

theorem fixedFeedback_slope (energy damping : ℝ) (positive : 0 < damping) (point : LightBand) (time : ℝ) :
    fixedFeedback energy damping positive point time=time^2*slopeFeedback energy damping positive point time := by
  unfold fixedFeedback oppositeFeedback orientedFeedback
  have branch (orientation : Bool) : phaseBranch energy damping positive (orientedShift orientation point) time=
      fun sign => time • bandSlope energy damping positive orientation sign point time := by
    funext sign
    exact phaseBranch_slope energy damping positive orientation sign point time
  change (fourGram (bandCoupling true point) (bandCoupling false point)
      (phaseBranch energy damping positive (orientedShift true point) time)+
    fourGram (bandCoupling true point) (bandCoupling false point)
      (phaseBranch energy damping positive (orientedShift false point) time))/2=_
  have scaled (orientation : Bool) :
      fourGram (bandCoupling true point) (bandCoupling false point)
        (fun sign => time • bandSlope energy damping positive orientation sign point time)=
      time^2*fourGram (bandCoupling true point) (bandCoupling false point)
        (fun sign => bandSlope energy damping positive orientation sign point time) := by
    simpa using! (fourGram_real_smul (E := FullMatterL2) (bandCoupling true point) (bandCoupling false point)
      time (fun sign => bandSlope energy damping positive orientation sign point time))
  rw [branch true,branch false,scaled true,scaled false,slopeFeedback]
  ring

theorem slopeFeedback_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (slopeFeedback energy damping positive).uncurry := by
  have gram (orientation : Bool) : Continuous (fun pair : LightBand×ℝ =>
      fourGram (bandCoupling true pair.1) (bandCoupling false pair.1)
        (fun sign => bandSlope energy damping positive orientation sign pair.1 pair.2)) := by
    simp_rw [fourGram_coordinates]
    have same := (bandCoupling_continuous true).comp (continuous_fst : Continuous (Prod.fst : LightBand×ℝ → LightBand))
    have opposite := (bandCoupling_continuous false).comp (continuous_fst : Continuous (Prod.fst : LightBand×ℝ → LightBand))
    have plus := bandSlope_continuous energy damping positive orientation true
    have minus := bandSlope_continuous energy damping positive orientation false
    exact continuous_const.mul
      ((((same.sub opposite).div_const 2).mul ((plus.sub minus).norm.pow 2)).add
        (((same.add opposite).div_const 2).mul ((plus.add minus).norm.pow 2)))
  exact ((gram true).add (gram false)).div_const 2

theorem slopeFeedback_initial (energy damping : ℝ) (positive : 0 < damping) (point : LightBand) :
    slopeFeedback energy damping positive point 0=(bandCoupling true point+bandCoupling false point)*
      oppositeNoise energy damping positive (bandShift point) 0 := by
  unfold slopeFeedback
  simp_rw [bandSlope_initial,fourGram_constant]
  unfold oppositeNoise phaseNoise orientedShift
  simp only [Bool.false_eq_true,↓reduceIte]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
