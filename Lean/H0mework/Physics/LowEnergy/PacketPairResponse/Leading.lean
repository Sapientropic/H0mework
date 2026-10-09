import H0mework.Physics.LowEnergy.PacketPairResponse.Branch
import H0mework.Physics.LowEnergy.PacketPairResponse.Quadratic

/-! The actual opposite Fourier pair, with both growth signs retained, generates its quadratic-time feedback weight. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace PacketFourier PacketNoise Filter Topology
noncomputable section

def orientedFeedback (same opposite : ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) : ℝ :=
  fourGram same opposite (phaseBranch energy damping positive shift time)

def oppositeFeedback (same opposite : ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) : ℝ :=
  (orientedFeedback same opposite energy damping positive shift time+
    orientedFeedback same opposite energy damping positive (-shift) time)/2

theorem orientedFeedback_limit (same opposite : ℝ) (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    Tendsto (fun time => orientedFeedback same opposite energy damping positive shift time/time^2) (𝓝[≠] 0)
      (𝓝 ((same+opposite)*phaseNoise energy damping positive shift 0)) :=
  fourGram_leading same opposite (phaseBranch energy damping positive shift)
    (phasePacket energy damping positive shift 0)
    (phaseBranch_initial energy damping positive shift) (phaseBranch_initial_derivative energy damping positive shift)

theorem oppositeFeedback_limit (same opposite : ℝ) (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    Tendsto (fun time => oppositeFeedback same opposite energy damping positive shift time/time^2) (𝓝[≠] 0)
      (𝓝 ((same+opposite)*oppositeNoise energy damping positive shift 0)) := by
  have generated := ((orientedFeedback_limit same opposite energy damping positive shift).add
    (orientedFeedback_limit same opposite energy damping positive (-shift))).div_const 2
  convert! generated using 1
  · funext time
    unfold oppositeFeedback
    ring
  · unfold oppositeNoise
    ring

theorem oppositeFeedback_tensor (sameT oppositeT sameL oppositeL weight : ℝ)
    (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    oppositeFeedback (sameT+(sameL-sameT)*weight) (oppositeT+(oppositeL-oppositeT)*weight)
      energy damping positive shift time=
    oppositeFeedback sameT oppositeT energy damping positive shift time+
      (oppositeFeedback sameL oppositeL energy damping positive shift time-
        oppositeFeedback sameT oppositeT energy damping positive shift time)*weight := by
  unfold oppositeFeedback orientedFeedback
  simp_rw [fourGram_tensor]
  ring

theorem oppositeFeedback_source_limit (same opposite : ℝ) (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    Tendsto (fun time => oppositeFeedback same opposite energy damping positive shift time/time^2) (𝓝[≠] 0)
      (𝓝 ((same+opposite)*
        (Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
          (Stage9DEF.Compatibility.responseMatrix (FullQuantum.HistoryPrepared.sourceMother
            (oppositeObservable energy damping positive shift 0 0)))).re)) := by
  rw [opposite_source_diagonal,Complex.ofReal_re]
  exact oppositeFeedback_limit same opposite energy damping positive shift

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
