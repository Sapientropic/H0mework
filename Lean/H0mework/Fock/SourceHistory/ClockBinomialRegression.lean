import H0mework.Fock.SourceHistoryClock.BinomialAction
import H0mework.Fock.SourceHistory.ClockPosteriorRegression

/-! The new moment resolves the exact old-clock source relation and the original square task. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Controls

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceWeightedRecovery.Runtime.Actor.History

noncomputable section

def sourceSecondDifference (depth : Nat) : Nat →₀ ℤ :=
  SourceOperationNative.point (runtimeAt (depth + 2)) -
    (2 : ℤ) • SourceOperationNative.point (runtimeAt (depth + 1)) + SourceOperationNative.point (runtimeAt depth)

theorem source_difference_projects (depth : Nat) :
    projection (sourceSecondDifference depth) = Frame.secondEffect depth := by
  simp only [sourceSecondDifference, map_add, map_sub, map_smul]
  exact (secondEffect_is_actual depth).symm

theorem original_relation_resolved (depth : Nat) :
    SourceClockModel.projection (sourceSecondDifference depth) = 0 ∧
      secondRead (projection (sourceSecondDifference depth)) = 1 ∧
      squareRead (projection (sourceSecondDifference depth)) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (forget_source (sourceSecondDifference depth)).symm.trans
      ((congrArg forgetClock (source_difference_projects depth)).trans
        ((forget_zero_iff _).mpr ⟨Frame.mass_secondEffect depth, Frame.clock_secondEffect depth⟩))
  · exact (congrArg secondRead (source_difference_projects depth)).trans (Frame.second_secondEffect depth)
  · exact (congrArg squareRead (source_difference_projects depth)).trans (square_secondEffect depth)

theorem source_square_linear_recovery (bound depth : Nat) (index : Fin (bound + 1)) :
    (pastSquare (depth + 1) (Fock.point (index.val + (depth + 1))) : ℂ) = Clock.sourceSquare bound index := by
  rw [pastSquare_point, Clock.sourceSquare, Clock.task_source]
  push_cast
  rfl

end
end SourceBinomialClock.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
