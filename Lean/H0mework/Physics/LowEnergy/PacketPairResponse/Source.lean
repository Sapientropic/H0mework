import H0mework.Physics.LowEnergy.PacketPairResponse.Limit
import H0mework.Physics.LowEnergy.PacketPairResponse.Time

/-! The actual fixed-probe integral consumes the original Stage10 whole-current
pair at every pair of times. It never projects between its two factors. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace PacketFourier HistoryPrepared Stage9DEF VertexTensor
noncomputable section

def sourceBranchGram (energy damping : ℝ) (positive : 0 < damping) (shift : Position)
    (first second : Bool) (time : ℝ) : ℂ :=
  ∫ left in (0 : ℝ)..time, ∫ right in (0 : ℝ)..time,
    (starRingEnd ℂ) (phaseKernel shift first time left)*phaseKernel shift second time right*
      State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (sourceMother
          (phaseCovarianceObservable energy damping positive shift shift left right)))

theorem sourceBranchGram_read (energy damping : ℝ) (positive : 0 < damping) (shift : Position)
    (first second : Bool) (time : ℝ) :
    sourceBranchGram energy damping positive shift first second time=
      inner ℂ (phaseBranch energy damping positive shift time first)
        (phaseBranch energy damping positive shift time second) :=
  phaseBranch_source_twoPoint energy damping positive shift shift first second time time

def sourceFourFeedback (same opposite : ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) : ℝ :=
  (1/4 : ℝ)*∑ orientation : Bool, ∑ first : Bool, ∑ second : Bool,
    (if first=second then same else opposite)*
      (sourceBranchGram energy damping positive (if orientation then shift else -shift) first second time).re

theorem sourceFourFeedback_read (same opposite : ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) :
    sourceFourFeedback same opposite energy damping positive shift time=
      oppositeFeedback same opposite energy damping positive shift time := by
  unfold sourceFourFeedback
  simp_rw [sourceBranchGram_read]
  simp only [oppositeFeedback,orientedFeedback,fourGram,Fintype.sum_bool,
    Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
  ring

theorem bandResponse_source (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    bandResponse energy damping positive time=fourierDensity*
      ∫ point : LightBand, sourceFourFeedback (bandCoupling true point) (bandCoupling false point)
        energy damping positive (bandShift point) time ∂bandMeasure := by
  simp_rw [sourceFourFeedback_read]
  rfl

theorem bandLeading_nonnegative (energy damping : ℝ) (positive : 0 < damping) :
    0 ≤ bandLeading energy damping positive := by
  unfold bandLeading
  apply mul_nonneg (by unfold fourierDensity; positivity)
  apply integral_nonneg
  intro point
  exact mul_nonneg (add_nonneg
      (fixedMomentumCoupling_positive true _ (band_small point)).le
      (fixedMomentumCoupling_positive false _ (band_small point)).le)
    (oppositeNoise_nonnegative energy damping positive (bandShift point) 0)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
