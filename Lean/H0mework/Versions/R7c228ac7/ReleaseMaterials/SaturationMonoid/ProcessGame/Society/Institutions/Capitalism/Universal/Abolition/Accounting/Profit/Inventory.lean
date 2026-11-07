import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Trace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Physical

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

abbrev Vector := Financial.MaterialChange (Party := Party) (Good := Good)

/-- Productive effects include their actual inputs, use and adoption costs. -/
def productionAt (item : ExecutionItem Party Good Port Technology Instrument) :
    Vector (Party := Party) (Good := Good) :=
  match item.request.operation with
  | .produce _ | .use .. | .revise .. => Financial.materialChange law item.before item.request
  | _ => 0

/-- Original claims and transfers change holders' positions, not material output.
Repayment is absent because cash and retirement cancel in the original full account. -/
def transferAt (item : ExecutionItem Party Good Port Technology Instrument) :
    Vector (Party := Party) (Good := Good) :=
  match item.request.operation with
  | .issue .. | .assign .. => Financial.value law (Financial.claimChange law item.before item.request)
  | .transfer .. => Financial.materialChange law item.before item.request
  | _ => 0

omit [DecidableEq Instrument] in
theorem every_original_operation_separates_production_and_existing_positions
    (item : ExecutionItem Party Good Port Technology Instrument) :
    Financial.fullChange law item.before item.request = productionAt law item + transferAt law item := by
  cases operation : item.request.operation with
  | settle instrument debtor holder quantity =>
      rw [Financial.settlement_is_neutral_for_every_original_bearer law _ _ instrument debtor holder quantity operation]
      simp [productionAt,transferAt,operation]
  | _ =>
      by_cases accepted : law.Valid item.before item.request <;>
        simp [Financial.fullChange,Financial.materialChange,Financial.claimChange,
          Financial.rawClaimChange,Financial.flowVector,productionAt,transferAt,operation,
          RawLaw.actualCredit,RawLaw.actualDebit,RawLaw.credit,RawLaw.debit,accepted]

def production (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    Vector (Party := Party) (Good := Good) := (items.map (productionAt law)).sum

def transfers (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    Vector (Party := Party) (Good := Good) := (items.map (transferAt law)).sum

def fullIncome (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    Vector (Party := Party) (Good := Good) :=
  Financial.inventoryMaterial law items + Financial.value law (Financial.inventoryClaims law items)

omit [DecidableEq Instrument] in
theorem every_original_inventory_separates_production_and_existing_positions
    (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    fullIncome law items = production law items + transfers law items := by
  induction items with
  | nil => simp [fullIncome,production,transfers,Financial.inventoryMaterial,Financial.inventoryClaims]
  | cons item rest inherited =>
      have first := every_original_operation_separates_production_and_existing_positions law item
      simp only [fullIncome,Financial.inventoryMaterial,Financial.inventoryClaims,List.map_cons,
        List.sum_cons,map_add] at inherited ⊢
      simp only [Financial.fullChange] at first
      simp only [production,transfers,List.map_cons,List.sum_cons] at inherited ⊢
      ext cell
      have one := congrArg (fun value : Vector (Party := Party) (Good := Good) => value cell) first
      have later := congrArg (fun value : Vector (Party := Party) (Good := Good) => value cell) inherited
      simp only [Finsupp.add_apply] at one later ⊢
      linarith

omit [DecidableEq Instrument] in
theorem an_original_repayment_has_no_new_full_account_income
    (item : ExecutionItem Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : item.request.operation = .settle instrument debtor holder quantity) :
    productionAt law item = 0 ∧ transferAt law item = 0 ∧
      Financial.fullChange law item.before item.request = 0 :=
  ⟨by simp [productionAt,operation],by simp [transferAt,operation],
    Financial.settlement_is_neutral_for_every_original_bearer law _ _ instrument debtor holder quantity operation⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit
