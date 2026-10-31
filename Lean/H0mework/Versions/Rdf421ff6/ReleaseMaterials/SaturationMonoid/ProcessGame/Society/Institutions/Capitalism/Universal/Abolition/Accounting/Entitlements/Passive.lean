import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Valuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Financing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Actual absence of a new contribution or disposition request. Waiting may
advance the original clock, but is not an event authorizing a new income claim. -/
def Passive (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ request ∈ word,request.operation = .present

theorem a_presentation_does_not_spend_or_mint
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (passive : request.operation = .present) :
    law.step before request = before := by
  by_cases valid : law.Valid before request
  · simp [RawLaw.step,valid,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,RawLaw.nextClaims,passive,flowAt]
  · exact law.rejected_preserves_current before request valid

theorem continued_possession_cannot_generate_stock_claims_or_control
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (passive : Passive word) :
    (law.next before word).stock = before.stock ∧
      (law.next before word).claims = before.claims ∧
      (law.next before word).technology = before.technology := by
  have same : ∀ current index,(law.execute current index word).final = current := by
    induction word with
    | nil => exact fun _ _ => rfl
    | cons request rest inherited =>
        intro current index
        change (law.execute (law.step current request) (index + 1) rest).final = current
        rw [a_presentation_does_not_spend_or_mint law current request (passive request List.mem_cons_self)]
        exact inherited (fun item member => passive item (List.mem_cons_of_mem request member)) current (index + 1)
  have actual := same before 0
  change (law.execute before 0 word).final.stock = before.stock ∧
    (law.execute before 0 word).final.claims = before.claims ∧
    (law.execute before 0 word).final.technology = before.technology
  exact ⟨congrArg RawCurrent.stock actual,congrArg RawCurrent.claims actual,congrArg RawCurrent.technology actual⟩

theorem passive_execution_items_are_still_presentations
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (passive : Passive word)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (member : item ∈ law.rawItems before word) : item.request.operation = .present := by
  have words := law.inventory_requests_exact before 0 word
  apply passive item.request
  rw [← words]
  exact List.mem_map.mpr ⟨item,member,rfl⟩

theorem no_valuation_or_possession_is_a_disbursement
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (passive : Passive word)
    (terms : PublicFunction.Financing.Terms Party Instrument) :
    ¬ Nonempty (PublicFunction.Financing.Disbursement law before word terms) := by
  rintro ⟨receipt⟩
  have actual := passive_execution_items_are_still_presentations law before word passive receipt.issue receipt.issue_mem
  rw [receipt.issue_kind] at actual
  cases actual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements
