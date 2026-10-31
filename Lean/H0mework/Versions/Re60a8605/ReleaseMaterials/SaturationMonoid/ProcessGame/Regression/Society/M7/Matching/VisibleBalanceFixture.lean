import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Matching.VisibleBalance
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.NaturalReconstructionNoGoRegression

/-!
# M7 visible matching balance fixture

The matching computation lives entirely on the independently presented M5
normalized image.  It positively balances the image's terminal value while
making no claim that the image identifies either actual source occurrence or
its fulfilled authority residual.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7VisibleBalanceFixture

noncomputable section

open Classical.Independent.SourceFirstSingletonGame
open M5SourceFirstCrossOccurrenceResidual
open M6NormalizedAuthorityObserverFixture
open M6FaithfulReconstructionNoGoRegression
open Matching

/-- Visible terminal settlement readout of the one normalized image. -/
def visibleTerminalValue (_image : NormalizedImage) : Option ℚ :=
  game.utility uniqueProfile uniquePlayer

theorem visibleTerminalValue_exact :
    visibleTerminalValue commonImage = some 7 :=
  utility_uniqueProfile

/-- Both sides of matching consume the same visible settlement computation;
neither side carries a credit lineage or hidden-authority field. -/
def visibleMatchingBalance :
    VisibleBalanceReadout NormalizedImage (Option ℚ) where
  leftBalance := visibleTerminalValue
  rightBalance := visibleTerminalValue

theorem common_image_balances :
    visibleMatchingBalance.BalancedAt commonImage :=
  ⟨rfl⟩

theorem positive_visible_balance :
    Nonempty visibleMatchingBalance.BalancedImage :=
  visibleMatchingBalance.balancedImage_has_positive_witness
    commonImage rfl

theorem matched_value_is_nonzero_terminal_value :
    visibleMatchingBalance.leftBalance commonImage = some 7 ∧
      visibleMatchingBalance.rightBalance commonImage = some 7 :=
  ⟨visibleTerminalValue_exact, visibleTerminalValue_exact⟩

theorem both_actual_paths_have_same_visible_balance :
    visibleMatchingBalance.leftBalance
        (societyObserver.forget leftPath) =
      visibleMatchingBalance.leftBalance
        (societyObserver.forget rightPath) :=
  rfl

end
end M7VisibleBalanceFixture
end Society
end ProcessGame
end SaturationMonoid
