import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Compiler
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalRecipe
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Frontier

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.JointOpening

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (originalRequirements)
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Conflict.Consumers.Evolving (sourceInput)
open Clearance
open Clearance.Joint.OriginalExchange hiding offers
open Supply.Consumers (refillWord)
open TerminalPeace.Supply (personalWord)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

/-- The original personal approvals read the reached inventories. The
offered refill can be installed at any cut with the protected stock. -/
def offers : ProductionMenu Bool Bool Bool Unit Unit :=
  ⟨[OriginalRecipe.offer], fun past _ person =>
    decide (18 ≤ (endAt Original.seed past).raw.stock person false ∧
      0 ≤ (endAt Original.seed past).raw.stock person true)⟩

private abbrev selected : ProductionChoice offers := some ⟨0, Nat.zero_lt_one⟩
private abbrev people : List Bool := productionRoster Original.seed loss closed selected
private abbrev original := originalRaw loss
private abbrev exchangeCut := prefixRaw loss closed

private def snapshot : Original.Raw :=
  deliveredRaw (deliveredRaw (deliveredRaw (Original.snapshot 129 113) food (1 / 2)) supply 6) claim 6

private theorem exact_exchange_cut : exchangeCut = snapshot := by
  change prefixRaw loss (beforePayment ++ installment false claim 6) = _
  rw [paid.raw, before_payment_raw]
  rfl

private theorem approved : ProductionApproved Original.seed loss closed selected := by
  intro person _
  apply decide_eq_true
  change 18 ≤ exchangeCut.stock person false ∧ 0 ≤ exchangeCut.stock person true
  rw [exact_exchange_cut]
  cases person <;> decide +kernel

private theorem installed_programme :
    productionInput Original.seed loss closed selected = OriginalRecipe.programme := by
  have actual := production_at_an_authorized_cut Original.seed loss closed _ paid.ready approved
  rw [actual, sourceInput]
  rfl

private theorem original_people_present (person : Bool) : person ∈ people :=
  production_roster_keeps_original_bearers Original.seed loss closed selected
    (OriginalService.each_original_bearer_remains_listed loss person)

private theorem everyone (person : Bool) : person ∈ ([false, true] : List Bool) := by
  cases person <;> decide

private theorem reads_every_original_need (atCut : Original.Raw) {cell : Bool × Use × Bool × ℚ}
    (listed : cell ∈ originalRequirements OriginalRecipe.programme atCut people) :
    cell ∈ originalRequirements OriginalRecipe.programme atCut [false, true] := by
  obtain ⟨person, _, required⟩ := List.mem_flatMap.mp listed
  exact List.mem_flatMap.mpr ⟨person, everyone person, required⟩

private theorem the_period_pays_the_source_roster :
    Supply.Period OriginalRecipe.programme original exchangeCut people refillWord := by
  have checked := OriginalRecipe.paidAt original exchangeCut [false, true] refillWord
    (by rw [exact_exchange_cut]; decide +kernel)
  refine ⟨fun item seen => ?_, fun cell listed => ?_, fun cell listed => ?_, checked.positiveClock⟩
  · have actual := checked.own item seen
    exact ⟨actual.operation, original_people_present item.request.signer, actual.noConsent, actual.valid⟩
  · exact checked.originalFloor cell (reads_every_original_need original listed)
  · exact checked.currentFloor cell (reads_every_original_need exchangeCut listed)

private def checkedRecipe : Recipe OriginalRecipe.programme original people exchangeCut 1 :=
  OriginalRecipe.recipeOfChecks original exchangeCut people the_period_pays_the_source_roster
    (fun person _ => OriginalRecipe.paidAt original exchangeCut [person] (personalWord person) (by
      rw [exact_exchange_cut]
      cases person <;> decide +kernel))
    (by rw [exact_exchange_cut]; decide +kernel)
    ⟨false, true, by rw [exact_exchange_cut]; decide +kernel⟩

private theorem cast_recipe_preserves_word {input changed :
    Capitalism.Universal.Root.ProgrammeSource.Input Bool Bool Bool Unit Unit} (same : input = changed)
    (recipe : Recipe input original people exchangeCut 1) :
    (same ▸ recipe : Recipe changed original people exchangeCut 1).move.word = recipe.move.word := by
  cases same
  rfl

private def openingRecipe :
    Recipe (productionInput Original.seed loss closed selected) original people exchangeCut 1 :=
  installed_programme.symm ▸ checkedRecipe

private def opening : OpeningAt loss replies reserve [grow] offers closed where
  first := first_production_precedes_the_closed_word
  inventory := every_original_material_position_keeps_the_reserve
  eligible := paid.eligible
  ready := paid.ready
  paid := whole_original_row_is_paid
  choice := selected
  approved := approved
  quantum := 1
  recipe := openingRecipe
  starts := by
    have exactWord : openingRecipe.move.word = refillWord :=
      (cast_recipe_preserves_word installed_programme.symm checkedRecipe).trans rfl
    rw [exactWord]
    exact ⟨rfl, TerminalPeace.Supply.grow false, List.mem_cons_self, false, rfl⟩

/-- The production approval uses current stock, and the same compiler
finds a productive paid opening among the whole joint frontier. -/
theorem the_actual_exchange_installs_the_peace_fixed_point
    (policyReplies : Replies Bool Bool Bool Unit Unit) :
    ∃ first credit peace,
      compilePeace loss replies reserve [grow] offers policyReplies = .installed first credit peace ∧
      peace.word.length ≤ 9 ∧
      peace.entry.current.ledger.stack.balances.map Prod.fst =
        (Occurrence.originState loss).stack.balances.map Prod.fst ∧
      (∀ policy start bound,
        ∃ n ≥ start, bound < (history policyReplies peace.entry.current policy n).physical.raw.clock) ∧
      let current := peace.entry.current
      let renewal := dispatch policyReplies current .renew
      renewal.visit.read.effect.isAccepted = true ∧
      (⟨current.ledger.world,
        (Installation.Core.action current.ledger renewal.visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
          AnyAuthoritativeRootCurrent) = renewal.next.ledger.resident.erase ∧
      (∀ row ∈ renewal.next.ledger.stack.balances, row.2.remaining = 0) := by
  obtain ⟨first, credit, peace, installed⟩ :=
    (compilePeace_installs_exactly_when_the_original_source_can_pay_and_renew
      loss replies reserve [grow] offers policyReplies).mpr
      ⟨opening_production_is_written, credit_first, closed, ⟨opening⟩⟩
  let renewal := dispatch policyReplies peace.entry.current .renew
  refine ⟨first, credit, peace, installed, peace.earliest closed ⟨opening⟩,
    peace.entry.every_old_address_is_retained, peace.fixed.cofinal, renewal.realWrite, renewal.wholeNext, ?_⟩
  intro row present
  exact peace.fixed.oldPaid row (renewal.rows ▸ present)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.JointOpening
