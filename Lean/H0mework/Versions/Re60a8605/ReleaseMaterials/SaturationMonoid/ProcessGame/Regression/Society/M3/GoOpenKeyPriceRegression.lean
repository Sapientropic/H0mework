import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Obligation.OpenKeyPriceReadout
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G6ClosureGainRegression

/-!
# G6 direct consumer for the M3 price-domain law

The exact G6 target face is consumed as a key-level readout.  This file does
not identify a Go key with a framework obligation or strong settlement.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M3GoOpenKeyPriceRegression

open Price
open Go Obligation
open Go.G6ClosureGainRegression

/-- The closure-gain fixture has settled every generated key. -/
theorem gainUpdate_targetFace_empty : gainUpdate.targetFace = ∅ := by
  decide

theorem gainUpdate_openKey_isEmpty :
    IsEmpty (GeneratedOpenKeyAt gainUpdate) := by
  refine ⟨?_⟩
  rintro ⟨key, member⟩
  rw [gainUpdate_targetFace_empty] at member
  simp at member

def gainZeroObserver : OpenKeyPriceObserverAt gainUpdate Int :=
  PriceObserverAt.zero

/-- Positive closure gain cannot manufacture a price domain after the exact
target face has become empty. -/
theorem positive_closureGain_does_not_create_price_domain :
    closureGain gainUpdate = 2 ∧
      ¬ Nonempty (PriceObservationAt gainZeroObserver) := by
  exact ⟨one_move_two_obligations_gain_gt_one.1,
    noOpenKeyPrice_of_targetFace_empty gainUpdate
      gainUpdate_targetFace_empty gainZeroObserver⟩

def debtControlOpenKey : GeneratedOpenKeyAt debtUpdate :=
  ⟨.generatedDebt .control, by decide⟩

def debtZeroObserver : OpenKeyPriceObserverAt debtUpdate Int :=
  PriceObserverAt.zero

def debtZeroObservation : PriceObservationAt debtZeroObserver :=
  zeroPriceObservation debtControlOpenKey

/-- A generated open debt admits a genuine zero-valued observation; zero is
not confused with absence of the observer domain. -/
theorem generated_debt_has_defined_zero_price :
    Nonempty (GeneratedOpenKeyAt debtUpdate) ∧
      Nonempty (PriceObservationAt debtZeroObserver) ∧
      debtZeroObservation.value = 0 :=
  ⟨⟨debtControlOpenKey⟩, ⟨debtZeroObservation⟩, rfl⟩

end M3GoOpenKeyPriceRegression
end Society
end ProcessGame
end SaturationMonoid
