import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.NoRetake
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Read

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Settled

open Source.Program Innovation
open Priority

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

private theorem no_extraction_step
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (noTake : ¬ Policy.CompulsoryTake request.operation)
    (noFinance : ¬ Policy.FinancialOperation request.operation)
    (person : Party) (good : Good) :
    (law.step current request).stock person good ≤ current.stock person good := by
  by_cases valid : law.Valid current request
  · have debit : 0 ≤ flowAt (law.debit current request) person good :=
      amount_nonnegative _ valid.2.2.2.1 (person,good)
    have credit : flowAt (law.credit current request) person good = 0 := by
      cases operation : request.operation <;>
        simp_all [Policy.CompulsoryTake,Policy.FinancialOperation,RawLaw.credit,flowAt,amount]
    have balance := law.material_step_balance current request person good
    simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos valid,credit] at balance
    linarith
  · rw [law.rejected_preserves_current current request valid]

theorem a_word_without_extraction_or_finance_cannot_raise_any_stock
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (noTake : ∀ request ∈ word, ¬ Policy.CompulsoryTake request.operation)
    (noFinance : ∀ request ∈ word, ¬ Policy.FinancialOperation request.operation)
    (person : Party) (good : Good) :
    (law.next current word).stock person good ≤ current.stock person good := by
  have actual : ∀ (start : RawCurrent Party Good Technology Instrument) (index : Nat),
      (law.execute start index word).final.stock person good ≤ start.stock person good := by
    induction word with
    | nil => exact fun _ _ => le_rfl
    | cons request rest inherited =>
      intro start index
      exact le_trans
        (inherited (fun next member => noTake next (List.mem_cons_of_mem _ member))
          (fun next member => noFinance next (List.mem_cons_of_mem _ member))
          (law.step start request) (index + 1))
        (no_extraction_step law start request (noTake _ List.mem_cons_self)
          (noFinance _ List.mem_cons_self) person good)
  exact actual current 0

variable {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

theorem the_paid_source_gate_prevents_actual_gain_for_every_original_bearer
    (claim : Responsibility.Family.Claim source past nature response)
    (state : Responsibility.Family.State claim)
    (law : RawLaw Party Good Port Technology Instrument) (members : List Party)
    (proposal : RawEvent Party Good Port Technology Instrument)
    (paid : Responsibility.Family.State.isPaid claim state)
    (person : Party) (good : Good) :
    (law.next state.raw (Policy.evaluate claim state law members proposal).executableWord).stock person good ≤
      state.raw.stock person good :=
  a_word_without_extraction_or_finance_cannot_raise_any_stock law state.raw _
    (Policy.accepted_paid_prefix_has_no_new_compulsory_request claim state law members paid
      (Policy.evaluate claim state law members proposal).accepted)
    (Policy.accepted_prefix_has_no_financial_operation claim state law members
      (Policy.evaluate claim state law members proposal).accepted) person good

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Settled
