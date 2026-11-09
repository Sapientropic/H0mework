import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

inductive Exposure (Party Good Instrument : Type)
  | signature
  | stock (good : Good) (quantity : ℚ)
  | issue (instrument : Instrument) (creditor : Party) (quantity : ℚ)
  | reassignment (instrument : Instrument) (debtor creditor replacement : Party) (quantity : ℚ)
  | settlement (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ)

abbrev Question (Party Good Instrument : Type) := Party × Exposure Party Good Instrument

abbrev physical (cut : C) := Boundary.Actual.materialLaw cut

def netDebit (cut : C) (item : Item) (bearer : Party) (good : Good) : ℚ :=
  flowAt ((physical cut).actualDebit item.before item.request) bearer good -
    flowAt ((physical cut).actualCredit item.before item.request) bearer good

def materialQuestions (cut : C) (item : Item) : List (Question Party Good Instrument) :=
  ((physical cut).actualDebit item.before item.request).filterMap fun entry =>
    let quantity := flowAt ((physical cut).actualDebit item.before item.request) entry.1.1 entry.1.2
    if 0 < quantity then some (entry.1.1, .stock entry.1.2 quantity) else none

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
def financialQuestions (item : Item) : List (Question Party Good Instrument) :=
  match item.request.operation with
  | .issue instrument debtor creditor quantity =>
    if 0 < quantity then [(debtor, .issue instrument creditor quantity)] else []
  | .assign instrument debtor creditor replacement quantity =>
    if 0 < quantity ∧ creditor ≠ replacement then
      let exposure := Exposure.reassignment instrument debtor creditor replacement quantity
      [(debtor, exposure), (creditor, exposure)]
    else []
  | .settle instrument debtor creditor quantity =>
    if 0 < quantity then
      let exposure := Exposure.settlement instrument debtor creditor quantity
      [(debtor, exposure), (creditor, exposure)]
    else []
  | _ => []

/-- The candidate's actual footprint has a personal signer and every
affected address, independently of the candidate's stated purpose. -/
def questions (cut : C) (item : Item) : List (Question Party Good Instrument) :=
  (item.request.signer, .signature) :: (materialQuestions cut item ++ financialQuestions item)

theorem signer_is_asked (cut : C) (item : Item) :
    (item.request.signer, .signature) ∈ questions cut item :=
  List.mem_cons_self

theorem a_positive_actual_debit_asks_its_actual_bearer (cut : C) (item : Item) (bearer : Party) (good : Good)
    (positive : 0 < flowAt ((physical cut).actualDebit item.before item.request) bearer good) :
    (bearer, .stock good (flowAt ((physical cut).actualDebit item.before item.request) bearer good)) ∈
      questions cut item := by
  let law := physical cut
  let debit := law.actualDebit item.before item.request
  have present : ∃ entry ∈ debit, entry.1 = (bearer, good) := by
    by_contra absent
    have empty : flowAt debit bearer good = 0 :=
      amount_zero_of_absent _ _ (fun entry listed same => absent ⟨entry, listed, same⟩)
    exact (lt_irrefl 0) (empty ▸ positive)
  obtain ⟨entry, listed, same⟩ := present
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  refine ⟨entry, listed, ?_⟩
  simp only [same, if_pos positive]

theorem nonpositive_actual_debit_is_nonpositive_net_debit
    (cut : C) (item : Item) (bearer : Party) (good : Good)
    (unspent : flowAt ((physical cut).actualDebit item.before item.request) bearer good ≤ 0) :
    netDebit cut item bearer good ≤ 0 := by
  let law := physical cut
  have nonnegative : 0 ≤ flowAt (law.actualCredit item.before item.request) bearer good := by
    by_cases accepted : law.Valid item.before item.request
    · rw [RawLaw.actualCredit, if_pos accepted]
      exact amount_nonnegative _ accepted.2.2.2.2.1 _
    · simp [RawLaw.actualCredit, accepted, flowAt, amount]
  exact sub_nonpos.mpr (unspent.trans nonnegative)

theorem the_actual_stock_change_is_the_negative_of_net_debit (cut : C) (item : Item) (bearer : Party) (good : Good) :
    ((physical cut).step item.before item.request).stock bearer good =
      item.before.stock bearer good - netDebit cut item bearer good := by
  unfold netDebit
  linarith [(physical cut).material_step_balance item.before item.request bearer good]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
