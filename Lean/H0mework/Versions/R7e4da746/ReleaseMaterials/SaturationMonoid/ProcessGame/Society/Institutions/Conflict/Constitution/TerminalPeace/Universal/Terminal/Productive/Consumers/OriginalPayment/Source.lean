import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Unbounded.Nonattainment.Native
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Offer

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (C compact returnAt sourceInput)
open Quantities.Execution
open Reparation.Actual (ReceiptAnswers payerCredit)
open Reparation.Actual.Allocation (Position originalItem)
open Occurrence.Unbounded.Nonattainment (loss born payment)
open ExposureGuard
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

noncomputable section

abbrev installment (quantity : ℚ) : Original.Word := [payment quantity, none]

def replies : ReceiptAnswers Original.seed := fun past input site person =>
  let request := (originalItem Original.seed past input site).request
  match request.operation with
  | .transfer true false [(false, quantity)] => decide (request.signer = true ∧ 0 < quantity)
  | .produce true => request.signer && person
  | _ => false

abbrev Snapshot (paid : ℚ) (base : ℚ := 113) := Original.snapshot (111 + paid) (base - paid)

private theorem legal {base : ℚ} (paid quantity : ℚ) (positive : 0 < quantity) (funded : quantity ≤ base - paid) :
    compact.law.Valid (Snapshot paid base) (returnAt quantity) := by
  unfold RawLaw.Valid
  refine ⟨⟨trivial, rfl⟩, ?_, trivial, ?_, ?_, ?_⟩
  · intro port listed
    change port ∈ [false] at listed
    rw [List.mem_singleton.mp listed]
    exact Or.inl rfl
  · intro item listed
    change item ∈ [((true, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro item listed
    change item ∈ [((false, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro item listed
    change item ∈ [((true, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    change flowAt (locate true [(false, quantity)]) true false ≤ base - paid
    simpa [flowAt, amount, locate] using funded

variable (past : Original.Word) (paid quantity : ℚ)

private theorem cut_source : (endAt Original.seed past).native.input = compact :=
  (endAt_input Original.seed past).trans sourceInput

variable {base : ℚ} (stock : (endAt Original.seed past).raw = Snapshot paid base)
  (ready : Ready (endAt Original.seed past)) (review : ReviewAvailable (endAt Original.seed past))
  (positive : 0 < quantity) (funded : quantity ≤ base - paid)

include stock positive funded in
private theorem legal_at_cut :
    (endAt Original.seed past).native.input.law.Valid (endAt Original.seed past).raw (returnAt quantity) := by
  rw [cut_source past, stock]
  exact legal paid quantity positive funded

include stock positive funded in
private theorem physical :
    (Physical.Public.interpreter (endAt Original.seed past).native.input).Valid
      (endAt Original.seed past).raw (returnAt quantity) :=
  PublicFunction.valid_physical _ _ _ (legal_at_cut past paid quantity stock positive funded)

include stock ready review positive funded

theorem actual_items :
    Boundary.Actual.items (endAt Original.seed past) (payment quantity) =
      [⟨0, (endAt Original.seed past).raw, returnAt quantity⟩] :=
  (the_selected_primitive_is_paid_by_the_original_root
    (queued (endAt Original.seed past) (returnAt quantity)) (returnAt quantity) ready
    (the_available_review_forwards_the_actual_requested_primitive _ _ review) rfl
    (physical past paid quantity stock positive funded)).2.2

theorem accounting_has_no_items :
    Boundary.Actual.items (endAt Original.seed (past ++ [payment quantity])) none = [] := by
  have work := the_actual_body_must_consume_its_original_native_head (endAt Original.seed past)
    (returnAt quantity) ready review rfl (physical past paid quantity stock positive funded)
  rw [endAt_append]
  exact Reparation.Transport.native_step_has_no_material_items none work

theorem the_return_has_no_new_damage :
    Boundary.Actual.damages (endAt Original.seed past) (payment quantity) Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have literal := damage.source_item
  rw [actual_items past paid quantity stock ready review positive funded] at literal
  have item := List.mem_singleton.mp literal
  have keys := original_key damage
  have valid := damage.actual_foreign_debit.2.1
  rw [item] at keys valid
  unfold keysAt at keys
  rw [RawLaw.actualDebit, if_pos valid] at keys
  change damage.key ∈ [(true, true, false)] at keys
  have foreign := damage.actual_foreign_debit.1.1
  rw [List.mem_singleton.mp keys] at foreign
  exact foreign rfl

theorem original_item (site : Position Original.seed past (payment quantity)) :
    originalItem Original.seed past (payment quantity) site =
      ⟨0, (endAt Original.seed past).raw, returnAt quantity⟩ := by
  have listed : originalItem Original.seed past (payment quantity) site ∈
      Boundary.Actual.items (endAt Original.seed past) (payment quantity) := List.getElem_mem _
  rw [actual_items past paid quantity stock ready review positive funded] at listed
  exact List.mem_singleton.mp listed

theorem the_actual_reply (site : Position Original.seed past (payment quantity)) (person : Bool) :
    replies past (payment quantity) site person = true := by
  unfold replies
  dsimp only
  rw [original_item past paid quantity stock ready review positive funded site]
  simp [returnAt, positive]

theorem the_actual_delivery (site : Position Original.seed past (payment quantity)) :
    payerCredit Original.seed.native.input.law (originalItem Original.seed past (payment quantity) site)
      loss.key = quantity := by
  rw [original_item past paid quantity stock ready review positive funded site, sourceInput, stock]
  have allowed := legal paid quantity positive funded
  unfold returnAt at allowed
  change payerCredit compact.law ⟨0, Snapshot paid base, returnAt quantity⟩ (false, true, false) = quantity
  simp [payerCredit, returnAt, allowed, RawLaw.actualCredit, RawLaw.credit, locate, flowAt, amount,
    max_eq_right positive.le]

theorem the_return_and_its_accounting_are_eligible (anchor : Original.Word) :
    Occurrence.EligibleFrom Original.community replies anchor past (installment quantity) := by
  refine ⟨⟨⟨?_, fun site question _ _ => the_actual_reply past paid quantity stock ready review positive funded site question.1⟩,
    the_return_has_no_new_damage past paid quantity stock ready review positive funded⟩, ?_, trivial⟩
  · intro item listed
    change item ∈ Boundary.Actual.items (endAt Original.seed past) (payment quantity) at listed
    rw [actual_items past paid quantity stock ready review positive funded] at listed
    rw [List.mem_singleton.mp listed]
    exact legal_at_cut past paid quantity stock positive funded
  · have absent := accounting_has_no_items past paid quantity stock ready review positive funded
    exact ⟨no_material_is_admitted _ _ _ _ absent, Boundary.Actual.no_material_write_has_no_damage _ _ _ absent⟩

private theorem actual_trace :
    Trace (endAt Original.seed past) [returnAt quantity] (endAt Original.seed (past ++ installment quantity)) ∧
    Ready (endAt Original.seed (past ++ installment quantity)) ∧
    ReviewAvailable (endAt Original.seed (past ++ installment quantity)) := by
  rw [endAt_append]
  apply pay_checked_primitives (endAt Original.seed past) [returnAt quantity] 0 ready review
  · intro request member
    rw [List.mem_singleton.mp member]
    rfl
  · intro item member
    change item ∈ [⟨0, (endAt Original.seed past).raw, returnAt quantity⟩] at member
    rw [List.mem_singleton.mp member]
    exact physical past paid quantity stock positive funded

theorem the_original_cut_after_an_installment :
    (endAt Original.seed (past ++ installment quantity)).raw = Snapshot (paid + quantity) base ∧
    Ready (endAt Original.seed (past ++ installment quantity)) ∧
    ReviewAvailable (endAt Original.seed (past ++ installment quantity)) := by
  have execution := actual_trace past paid quantity stock ready review positive funded
  refine ⟨?_, execution.2⟩
  rw [execution.1.raw_is_the_complete_original_execution 0, cut_source past, stock]
  let interpreter := Physical.Public.interpreter compact
  have checked : interpreter.Valid (Snapshot paid base) (returnAt quantity) :=
    PublicFunction.valid_physical _ _ _ (legal paid quantity positive funded)
  change (interpreter.execute (Snapshot paid base) 0 [returnAt quantity]).final = _
  rw [show (interpreter.execute (Snapshot paid base) 0 [returnAt quantity]).final =
    interpreter.step (Snapshot paid base) (returnAt quantity) from rfl, RawLaw.step, if_pos checked]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [Snapshot, Original.snapshot, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
        returnAt, locate, flowAt, amount] <;> ring
  · rfl
  · rfl
  · rfl
  · rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment
