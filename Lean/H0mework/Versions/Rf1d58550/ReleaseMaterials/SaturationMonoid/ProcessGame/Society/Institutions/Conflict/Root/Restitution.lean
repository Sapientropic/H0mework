import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Head

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
open scoped BigOperators

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument

theorem trace_after_prefix (source target : C) (front suffix : Word)
    (trace : Runtime.Trace source (front ++ suffix) target) :
    Runtime.Trace (terminal source front) suffix target := by
  induction front generalizing source with
  | nil => exact trace
  | cons first front ih =>
      cases trace with
      | cons _ _ _ _ _ _ _ _ later => exact ih (Runtime.afterNative source first) later

theorem trace_before_prefix (source target : C) (front suffix : Word)
    (trace : Runtime.Trace source (front ++ suffix) target) :
    Runtime.Trace source front (terminal source front) := by
  induction front generalizing source with
  | nil => exact .nil source
  | cons first front ih =>
      cases trace with
      | cons _ _ _ _ ready review consents valid later =>
          exact .cons source first front _ ready review consents valid (ih (Runtime.afterNative source first) later)

private theorem a_paid_suffix_preserves_its_original_head
    {source target : C} {request : Req} (actual : Runtime.Trace source [request] target) :
    Runtime.Ready source ∧ Runtime.ReviewAvailable source ∧ request.consents = [] ∧
      (Physical.Public.interpreter source.native.input).Valid source.raw request ∧
        target = Runtime.afterNative source request := by
  cases actual with
  | cons _ _ _ _ ready review consents valid tail =>
      cases tail
      exact ⟨ready, review, consents, valid, rfl⟩

/-- Read the material restitution from the additional original receipt.
The destructive prefix is executed once, and the transfer leaves the
complete native financial account and all raw claims unchanged. -/
theorem a_paid_return_has_its_exact_original_effect
    {source : C} {word : Word} {request : Req} (paid : Paid source (word ++ [request]))
    (payer recipient : Party) (good : Good) (quantity : ℚ)
    (transfer : request.operation = .transfer payer recipient [(good, quantity)]) :
    let before := terminal source word
    let after := terminal source (word ++ [request])
    (∀ person lot, after.raw.stock person lot =
      before.raw.stock person lot - (if (payer, good) = (person, lot) then quantity else 0) +
        (if (recipient, good) = (person, lot) then quantity else 0)) ∧
      after.raw.claims = before.raw.claims ∧
      HEq (Transition.Exchange.nativeAccount after) (Transition.Exchange.nativeAccount before) := by
  dsimp only
  let before := terminal source word
  let after := terminal source (word ++ [request])
  have suffix := trace_after_prefix source after word [request] paid.trace
  obtain ⟨ready, review, consents, valid, same⟩ := a_paid_suffix_preserves_its_original_head suffix
  change after = Runtime.afterNative before request at same
  change (Physical.Public.interpreter before.native.input).Valid before.raw request at valid
  have effect := (Runtime.two_actual_root_steps_pay_and_consume_the_generated_primitive
    before request ready review consents valid).2
  refine ⟨?_, ?_, ?_⟩
  · intro person lot
    rw [show (terminal source (word ++ [request])).raw =
      (Physical.Public.interpreter before.native.input).step before.raw request from
        (congrArg (fun cut : C => cut.raw) same).trans effect]
    rw [RawLaw.step, if_pos valid]
    simp only [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, transfer,
      flowAt, locate, List.map_cons, List.map_nil, amount, List.sum_cons, List.sum_nil, add_zero]
    rfl
  · rw [show (terminal source (word ++ [request])).raw =
      (Physical.Public.interpreter before.native.input).step before.raw request from
        (congrArg (fun cut : C => cut.raw) same).trans effect]
    exact Transition.Exchange.a_material_transfer_retains_every_original_claim _ _ _ _ _ _ transfer
  · exact (Transition.Exchange.nativeAccount_heq_of_eq same).trans
      (Transition.Exchange.a_paid_transfer_keeps_the_literal_native_debt_account before request ready review consents
        valid payer recipient _ transfer)

/-- Reimbursement changes each coalition's own inventory by its exact
incidence. Counting both addresses preserves total stock in every good. -/
theorem a_paid_return_has_exact_coalition_incidence
    {source : C} {word : Word} {request : Req} (paid : Paid source (word ++ [request]))
    (payer recipient : Party) (good : Good) (quantity : ℚ)
    (transfer : request.operation = .transfer payer recipient [(good, quantity)])
    (coalition : Finset Party) (lot : Good) :
    ∑ person ∈ coalition, (terminal source (word ++ [request])).raw.stock person lot =
      (∑ person ∈ coalition, (terminal source word).raw.stock person lot) -
        (if payer ∈ coalition ∧ good = lot then quantity else 0) +
        (if recipient ∈ coalition ∧ good = lot then quantity else 0) := by
  have each := (a_paid_return_has_its_exact_original_effect paid payer recipient good quantity transfer).1
  calc
    _ = ∑ person ∈ coalition, ((terminal source word).raw.stock person lot -
        (if (payer, good) = (person, lot) then quantity else 0) +
        (if (recipient, good) = (person, lot) then quantity else 0)) :=
          Finset.sum_congr rfl (fun person _ => each person lot)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      by_cases same : good = lot
      · subst lot
        simp [Prod.mk.injEq]
      · simp [Prod.mk.injEq, same]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
