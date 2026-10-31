import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.FiniteExchangeFixture
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Settlement.AutomaticFullFulfillment

/-!
# M4 automatic whole-fulfillment regression

The existing four-leg exchange supplies one genuine `.fulfill` boundary
authority per generated leg.  The generic automatic fold, rather than a
handwritten four-edge run, produces the settlement current and exact full
fulfillment.  A separate nil continuation keeps an original leg open and
therefore cannot carry a full-fulfillment witness.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M4AutomaticFullFulfillmentRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture

/-- Existing process authority specialized to the exact terminal fulfilled
branch for every generated exchange leg. -/
def fulfillmentAuthority :
    ExactExchangeFulfillmentAuthority (exchangeLaw := exchangeLaw) :=
  fun _seed _leg =>
    { event := .fulfill
      receipt := ()
      disposition_eq := rfl }

abbrev automaticCompiler : SourceOwnedSettlementCompiler exchangeLaw :=
  AutomaticFullFulfillment.settlementCompiler fulfillmentAuthority

def automaticOccurrence : automaticCompiler.GeneratedSettlementOccurrence :=
  AutomaticFullFulfillment.settlementOccurrence
    fulfillmentAuthority exactExchangeSeed

noncomputable def automaticFullyFulfilled :
    FullyFulfilledExchangeAt automaticCompiler automaticOccurrence :=
  AutomaticFullFulfillment.fullyFulfilled
    fulfillmentAuthority exactExchangeSeed

/-- Every generated leg, not a caller-selected subcollection, reaches an
exact fulfilled archive. -/
theorem every_generated_leg_exactly_fulfilled
    (leg : automaticOccurrence.Leg automaticCompiler) :
    Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence leg) :=
  ⟨automaticFullyFulfilled.fulfilled leg⟩

/-- The concrete four-leg scope is consumed explicitly. -/
theorem all_four_legs_exactly_fulfilled :
    Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .a) ∧
      Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .b) ∧
      Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .c) ∧
      Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .d) :=
  ⟨every_generated_leg_exactly_fulfilled .a,
    every_generated_leg_exactly_fulfilled .b,
    every_generated_leg_exactly_fulfilled .c,
    every_generated_leg_exactly_fulfilled .d⟩

/-- The automatic continuation is indexed from the exact exchange target;
no start current or completed run is accepted from the caller. -/
def automaticWholeRun :
    P.Run (exactExchangeSeed.generatedState exchangeCompiler).current
      (automaticOccurrence.current automaticCompiler) :=
  automaticOccurrence.continuation automaticCompiler

theorem automatic_run_starts_at_exact_exchange_state :
    Nonempty
      (P.Run (exactExchangeSeed.generatedState exchangeCompiler).current
        (automaticOccurrence.current automaticCompiler)) :=
  ⟨automaticWholeRun⟩

/-- The settlement generated history is the existing exchange admission run
followed by the automatic fulfillment continuation. -/
theorem automatic_whole_generated_history :
    (automaticOccurrence.generatedState automaticCompiler).generated =
      NativeResponsibilityProcess.Run.concatRuns P
        (exactExchangeSeed.generatedState exchangeCompiler).generated
        automaticWholeRun :=
  rfl

theorem automatic_full_fulfillment_removes_open_fibre :
    IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence) :=
  automaticFullyFulfilled.openSettlement_isEmpty

/-! ## Nil/open control -/

def nilOpenCompiler : SourceOwnedSettlementCompiler exchangeLaw where
  SettlementSeed := Unit
  settlementAdmittedAt := fun _ => True
  exchangeSeed := fun _ => exactExchangeSeed
  continuation := fun _ =>
    ⟨(exactExchangeSeed.generatedState exchangeCompiler).current, .nil⟩

def exactNilOpenSeed : nilOpenCompiler.ExactSettlementSeed :=
  ⟨(), .after, by simp [Lifecycle.actualEventOccurrenceOf], rfl, trivial⟩

def nilOpenOccurrence : nilOpenCompiler.GeneratedSettlementOccurrence :=
  nilOpenCompiler.occurrenceOfSeed exactNilOpenSeed

def nilOpenA : OpenSettlementAt nilOpenCompiler nilOpenOccurrence where
  leg := .a
  obligation := exactExchangeSeed.obligation exchangeCompiler .a
  present := by
    exact exactExchangeSeed.generatedState_obligationSlot_get
      exchangeCompiler .a

theorem nil_open_occurrence_has_no_fully_fulfilled_witness :
    ¬ Nonempty
      (FullyFulfilledExchangeAt nilOpenCompiler nilOpenOccurrence) := by
  rintro ⟨fully⟩
  exact fully.openSettlement_isEmpty.false nilOpenA

structure AutomaticFullFulfillmentCertificate : Prop where
  fourLegScope : (exactExchangeSeed.legList exchangeCompiler).length = 4
  everyLeg : ∀ leg : automaticOccurrence.Leg automaticCompiler,
    Nonempty
      (FulfilledExchangeLegAt automaticCompiler automaticOccurrence leg)
  explicitFour :
    Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .a) ∧
      Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .b) ∧
      Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .c) ∧
      Nonempty (FulfilledExchangeLegAt automaticCompiler automaticOccurrence .d)
  startsAtExchange :
    Nonempty
      (P.Run (exactExchangeSeed.generatedState exchangeCompiler).current
        (automaticOccurrence.current automaticCompiler))
  wholeGeneratedHistory :
    (automaticOccurrence.generatedState automaticCompiler).generated =
      NativeResponsibilityProcess.Run.concatRuns P
        (exactExchangeSeed.generatedState exchangeCompiler).generated
        automaticWholeRun
  noOpenSettlement :
    IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence)
  nilControlIsOpen : Nonempty (OpenSettlementAt nilOpenCompiler nilOpenOccurrence)
  nilControlNotFulfilled :
    ¬ Nonempty
      (FullyFulfilledExchangeAt nilOpenCompiler nilOpenOccurrence)

theorem automaticFullFulfillmentDirectConsumer :
    AutomaticFullFulfillmentCertificate where
  fourLegScope := fixture_has_more_than_binary_scope
  everyLeg := every_generated_leg_exactly_fulfilled
  explicitFour := all_four_legs_exactly_fulfilled
  startsAtExchange := automatic_run_starts_at_exact_exchange_state
  wholeGeneratedHistory := automatic_whole_generated_history
  noOpenSettlement := automatic_full_fulfillment_removes_open_fibre
  nilControlIsOpen := ⟨nilOpenA⟩
  nilControlNotFulfilled :=
    nil_open_occurrence_has_no_fully_fulfilled_witness

end
end M4AutomaticFullFulfillmentRegression
end Society
end ProcessGame
end SaturationMonoid
