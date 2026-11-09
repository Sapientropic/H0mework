import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Step
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Raw" => RawCurrent Party Good M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  (roster : List Party) (answers : OwnerAnswers seed)
  (past : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)
  (input : Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)

/-- A locked review still exposes its literal original inventory. Changing
the proposed opcode cannot move its debit or receipt to another bearer. -/
theorem a_locked_review_cannot_route_around_an_original_question
    (closed : ¬ ReviewAvailable (endAt seed past)) (item : Item)
    (listed : item ∈ originalItems (seed := seed) past input)
    (question : Question Party Good Instrument) (asked : question ∈ questions (endAt seed past) item)
    (exposed : question.1 ∈ roster) (alternative : Input) :
    ¬ Authorized roster (withhold answers question.1) past alternative := by
  intro passed
  have same : originalItems (seed := seed) past input = originalItems (seed := seed) past alternative :=
    ForcePeace.Renewal.a_nonrecourse_review_selects_the_same_inventory (endAt seed past) closed input alternative
  have actual : item ∈ originalItems (seed := seed) past alternative := same ▸ listed
  obtain ⟨index, found⟩ := List.getElem?_of_mem actual
  obtain ⟨inside, exactItem⟩ := List.getElem?_eq_some_iff.mp found
  have signature := passed ⟨index, inside⟩ question (exactItem.symm ▸ asked) exposed
  rw [withholding_uses_the_original_personal_lane] at signature
  cases signature

theorem a_locked_review_cannot_route_around_a_withheld_grant
    (closed : ¬ ReviewAvailable (endAt seed past)) (item : Item)
    (listed : item ∈ originalItems (seed := seed) past input) (grant : Grants item.request)
    (person : Party) (exposed : person ∈ roster) (alternative : Input) :
    ∃ position : Fin (originalItems (seed := seed) past alternative).length,
      ¬ grantRule roster (withhold answers person) past alternative position := by
  have same : originalItems (seed := seed) past input = originalItems (seed := seed) past alternative :=
    ForcePeace.Renewal.a_nonrecourse_review_selects_the_same_inventory (endAt seed past) closed input alternative
  have actual : item ∈ originalItems (seed := seed) past alternative := same ▸ listed
  obtain ⟨index, found⟩ := List.getElem?_of_mem actual
  obtain ⟨inside, exactItem⟩ := List.getElem?_eq_some_iff.mp found
  refine ⟨⟨index, inside⟩, fun passed => ?_⟩
  exact any_withholding_original_bearer_vetoes_a_grant roster answers past alternative
    ⟨index, inside⟩ person exposed passed (exactItem.symm ▸ grant)

variable [DecidableEq Technology] [DecidableEq Community]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {community : Party → Community} {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}
  (prior : GuardedVisit base scope seed community anchor control)
  (offer : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument →
    Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

/-- Audit a tick that was already physically written. Refusing admission
cannot discard material, filings or the original live successor. -/
def auditWritten :=
  (prior.decide answers offer input, Receipts.writeAfter answers prior.state [input])

theorem a_physically_written_refusal_keeps_every_original_loss_and_exact_withheld_balance
    (person : Party)
    (refused : ¬ Admitted prior.roster (withhold answers person) prior.history input) :
    let written := auditWritten (withhold answers person) input prior offer
    input ∉ written.1.emitted ∧ Quantities.Recorded seed (prior.history ++ [input]) ∧
      (written.2.stack.balances.map Prod.fst = Reparation.Actual.originalLosses seed community (prior.history ++ [input])) ∧
      ∀ (loss : Reparation.Actual.Occurrence seed community) (balance : Reparation.Actual.Balance),
        loss.key.1 = person → (loss, balance) ∈ prior.state.stack.balances →
          ∃ row, written.2.read row = .inr (loss, balance) := by
  let written := auditWritten (withhold answers person) input prior offer
  refine ⟨fun chosen => refused (written.1.every_emitted_input_is_lawful input chosen).1,
    Quantities.record _ _, Receipts.writeAfter_origins _ _ _ _ prior.origins, ?_⟩
  intro loss balance same old
  subst person
  exact Receipts.the_exact_withheld_balance_is_read_on_the_original_successor answers prior.history [input]
    prior.state loss balance old

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
