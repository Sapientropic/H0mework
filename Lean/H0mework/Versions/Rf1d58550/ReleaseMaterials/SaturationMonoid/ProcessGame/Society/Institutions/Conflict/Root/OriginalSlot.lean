import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Incidence
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument

theorem nonfinancial_trace_keeps_the_entire_native_book {source target : C} {word : Word}
    (actual : Runtime.Trace source word target) (material : Settlement.NonFinancial word) :
    HEq (nativeAccount target) (nativeAccount source) := by
  induction actual with
  | nil => rfl
  | cons source request tail target ready review consents valid next inherited =>
      obtain ⟨item, original, _, consumed⟩ :=
        the_paid_primitive_has_one_literal_native_consumer source request ready review consents valid
      have head := material request List.mem_cons_self
      have nonfinancial : Accounting.Responsibility.NonFinancialOperation
          (item.instruction _ _ _).request.operation := by
        rw [original]
        change Accounting.Responsibility.NonFinancialOperation request.operation
        cases operation : request.operation <;>
          simp_all [Settlement.NonFinancialRequest, Accounting.Responsibility.NonFinancialOperation]
      have same := an_original_nonfinancial_item_keeps_the_literal_native_account
        _ _ _ item nonfinancial (nativeAccount (Runtime.afterBody source request))
      have successor := (consumed.trans (heq_of_eq same)).trans
        (the_paid_body_keeps_the_native_account source request ready)
      exact (inherited (fun next member => material next (List.mem_cons_of_mem _ member))).trans successor

/-- Even after the destructive and funding instructions, the principal
allocator reads precisely the opening book, including every earlier slot. -/
theorem a_shift_starts_settlement_with_the_complete_original_native_book
    {source : C} {front : Word} {levy settlement : Req} {index : Nat}
    (shift : Shift source front levy settlement index) :
    HEq (nativeAccount (terminal source (front ++ [levy]))) (nativeAccount source) := by
  have material : Settlement.NonFinancial (front ++ [levy]) := by
    intro request member
    rcases List.mem_append.mp member with earlier | last
    · exact shift.prior request earlier
    · rw [List.mem_singleton.mp last]
      unfold Settlement.NonFinancialRequest
      rw [shift.funding.funded]
      trivial
  have actual : Runtime.Trace source ((front ++ [levy]) ++ [settlement])
      (terminal source (front ++ [levy, settlement])) := by
    simpa only [List.append_assoc, List.singleton_append] using shift.execution.trace
  exact nonfinancial_trace_keeps_the_entire_native_book
    (trace_before_prefix source _ _ _ actual) material

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
