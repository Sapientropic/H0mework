import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Local

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Portfolio.Repair

open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (position : Position Party Instrument)

/-- Addresses are the original loan's two participants, not a supplied successful provider. -/
def suppliers : List Party := [position.debtor, position.creditor]

structure Order (law : RawLaw Party Good Port Technology Instrument) (position : Position Party Instrument) (current : RawCurrent Party Good Technology Instrument) where
  private mk ::
  failed : ExecutionItem Party Good Port Technology Instrument
  original : failed ∈ law.rawItems current (Repayment.candidate law position current)
  refused : ¬ law.Valid failed.before failed.request
  debit : (Party × Good) × ℚ
  required : debit ∈ law.debit failed.before failed.request
  shortfall : 0 < debit.2 - failed.before.stock debit.1.1 debit.1.2
  supplier : Party
  participant : supplier ∈ suppliers position
  distinct : supplier ≠ debit.1.1

def orders (current : RawCurrent Party Good Technology Instrument) : List (Order law position current) :=
  (law.rawItems current (Repayment.candidate law position current)).attach.flatMap fun failed =>
    if refused : ¬ law.Valid failed.val.before failed.val.request then
      (law.debit failed.val.before failed.val.request).attach.flatMap fun debit =>
        if shortfall : 0 < debit.val.2 - failed.val.before.stock debit.val.1.1 debit.val.1.2 then
          ((suppliers position).filter (fun supplier => decide (supplier ≠ debit.val.1.1))).attach.map fun supplier =>
            ⟨failed.val, failed.property, refused, debit.val, debit.property,
              shortfall, supplier.val, (List.mem_filter.mp supplier.property).1,
              by
                have selected : decide (supplier.val ≠ debit.val.1.1) = true :=
                  (List.mem_filter.mp supplier.property).2
                exact of_decide_eq_true selected⟩
        else []
    else []

/-- The suffix requests use the actual candidate-front result as their port context. -/
def Order.request {law : RawLaw Party Good Port Technology Instrument}
    {position : Position Party Instrument} {current : RawCurrent Party Good Technology Instrument} (order : Order law position current) : Request Party Good Port Technology Instrument :=
  let after := (law.execute current 0 (Repayment.candidate law position current)).final
  ⟨order.supplier, [], law.stockPort after.technology order.supplier order.debit.1.2, [],
    .transfer order.supplier order.debit.1.1
      [(order.debit.1.2, order.debit.2 - order.failed.before.stock order.debit.1.1 order.debit.1.2)]⟩

def word (current : RawCurrent Party Good Technology Instrument) : RawEvent Party Good Port Technology Instrument :=
  match Repayment.respond law position current with
  | .noPositiveDebt _ => []
  | .paid _ => Repayment.candidate law position current
  | .blocked .. => Repayment.candidate law position current ++ (orders law position current).map Order.request

inductive Kind where
  | clear | paid | blocked
  deriving DecidableEq, Repr

def kind (current : RawCurrent Party Good Technology Instrument) : Kind :=
  match Repayment.respond law position current with
  | .noPositiveDebt _ => .clear
  | .paid _ => .paid
  | .blocked .. => .blocked

theorem blocked_word_contains_the_candidate (current : RawCurrent Party Good Technology Instrument)
    (positive : 0 < Repayment.balance position current) (failed : ¬ Repayment.Ready law position current) :
    word law position current = Repayment.candidate law position current ++ (orders law position current).map Order.request := by
  unfold word Repayment.respond
  rw [dif_pos positive, dif_neg failed]

theorem paid_word_is_the_original_candidate (current : RawCurrent Party Good Technology Instrument)
    (positive : 0 < Repayment.balance position current) (ready : Repayment.Ready law position current) :
    word law position current = Repayment.candidate law position current := by
  unfold word Repayment.respond
  rw [dif_pos positive, dif_pos ready]

theorem every_order_has_a_real_front_refusal (current : RawCurrent Party Good Technology Instrument) (order : Order law position current)
    (positive : 0 < Repayment.balance position current) (failed : ¬ Repayment.Ready law position current) :
    order.failed ∈ law.rawItems current (word law position current) ∧ ¬ law.Valid order.failed.before order.failed.request := by
  rw [blocked_word_contains_the_candidate law position current positive failed]
  unfold RawLaw.rawItems
  rw [law.execute_append]
  exact ⟨List.mem_append_left _ order.original, order.refused⟩

theorem every_order_is_an_actual_requested_suffix (current : RawCurrent Party Good Technology Instrument) (order : Order law position current)
    (present : order ∈ orders law position current)
    (positive : 0 < Repayment.balance position current) (failed : ¬ Repayment.Ready law position current) :
    order.request ∈ word law position current := by
  rw [blocked_word_contains_the_candidate law position current positive failed]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨order, present, rfl⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Portfolio.Repair
