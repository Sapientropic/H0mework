import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Continuation.Runtime

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (point : Cursor code)

abbrev arrival := point.source.history.length+2+point.cut
abbrev Origin := Fin (arrival point+1)
abbrev account (origin : Origin point) := Financial.accountAt point.source.input origin.val
abbrev OldSlot (origin : Origin point) := Fin (account point origin).current.slots.length

def followed (origin : Origin point) (index : OldSlot point origin) :=
  Financial.Migration.actual point.source.input origin.val (arrival point-origin.val)
    index.val ((account point origin).current.slots.get index) (List.getElem?_eq_getElem index.isLt)

structure Template where
  request : Request Party Good Port (Mandate.State Party Technology) Instrument
  source : request ∈ code.actions
  instrument : Instrument
  debtor : Party
  creditor : Party
  amount : ℚ
  operation : request.operation = .settle instrument debtor creditor amount
  own : request.signer = debtor

def read (request : {request : Request Party Good Port (Mandate.State Party Technology) Instrument // request ∈ code.actions}) :
    Option (Template (code := code)) :=
  match operation : request.val.operation with
  | .settle instrument debtor creditor amount =>
    if own : request.val.signer = debtor then some ⟨request.val,request.property,instrument,debtor,creditor,amount,operation,own⟩ else none
  | _ => none

def templates : List (Template (code := code)) := code.actions.attach.filterMap read

variable (origin : Origin point) (template : Template (code := code))

def share (index : OldSlot point origin) : ℚ :=
  let slot := (followed point origin index).slot
  let claim := Financial.slotClaim point.source.input slot
  if claim.instrument = template.instrument ∧ claim.debtor = template.debtor then
    Financial.slotBalance point.source.input slot template.creditor else 0

def remaining : ℚ := ((List.finRange (account point origin).current.slots.length).map
  (share point origin template)).sum

theorem each_saved_original_share_is_nonnegative (index : OldSlot point origin) :
    0 ≤ share point origin template index := by
  dsimp only [share]
  split
  · exact (Financial.generated_sound point.source.input
      (Financial.accountAt point.source.input (origin.val+(arrival point-origin.val))) _
      (List.mem_of_getElem? (followed point origin index).present)).2 template.creditor
  · exact le_rfl

theorem original_remaining_is_nonnegative : 0 ≤ remaining point origin template :=
  List.sum_nonneg (fun value member => by
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    exact each_saved_original_share_is_nonnegative point origin template index)

def quantity : ℚ := max 0 (min template.amount (remaining point origin template))

def payment : Request Party Good Port (Mandate.State Party Technology) Instrument :=
  {template.request with operation := .settle template.instrument template.debtor template.creditor (quantity point origin template)}

def word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument :=
  if 0 < quantity point origin template then [payment point origin template] else []

theorem the_replayed_quantity_cannot_charge_more_than_the_original_shares :
    0 ≤ quantity point origin template ∧ quantity point origin template ≤ remaining point origin template :=
  ⟨le_max_left _ _,max_le (original_remaining_is_nonnegative point origin template) (min_le_right _ _)⟩

theorem a_skipped_positive_request_has_no_original_share_remaining
    (positive : 0 < template.amount) (skipped : word point origin template = []) :
    remaining point origin template = 0 ∧ ∀ index : OldSlot point origin,share point origin template index = 0 := by
  have quantityZero : quantity point origin template = 0 := by
    have notPositive : ¬ 0 < quantity point origin template := by
      intro paid
      simp only [word,if_pos paid,List.cons_ne_nil] at skipped
    exact le_antisymm (le_of_not_gt notPositive) (le_max_left _ _)
  have cleared : remaining point origin template = 0 := by
    have bound := le_max_right 0 (min template.amount (remaining point origin template))
    change _ ≤ quantity point origin template at bound
    rw [quantityZero] at bound
    by_cases order : template.amount ≤ remaining point origin template
    · rw [min_eq_left order] at bound
      exact False.elim (not_lt_of_ge bound positive)
    · rw [min_eq_right (le_of_not_ge order)] at bound
      exact le_antisymm bound (original_remaining_is_nonnegative point origin template)
  refine ⟨cleared,fun index => le_antisymm ?_ (each_saved_original_share_is_nonnegative point origin template index)⟩
  rw [← cleared]
  apply List.single_le_sum
  · intro value member
    obtain ⟨other,_,rfl⟩ := List.mem_map.mp member
    exact each_saved_original_share_is_nonnegative point origin template other
  · exact List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩

theorem the_saved_original_holder_keeps_its_actual_receipts_and_assignments (index : OldSlot point origin) :
    Financial.slotBalance point.source.input (followed point origin index).slot template.creditor +
        (followed point origin index).path.receivedBy point.source.input template.creditor =
      Financial.slotBalance point.source.input ((account point origin).current.slots.get index) template.creditor +
        (followed point origin index).path.assignedTo point.source.input template.creditor :=
  (followed point origin index).path.holder_conservation point.source.input template.creditor

theorem equal_retained_original_share_summaries_generate_the_same_word
    (other : Cursor code) (old : Origin other)
    (same : remaining point origin template = remaining other old template) :
    word point origin template = word other old template := by
  simp only [word,payment,quantity,same]
  rfl

theorem the_replayed_request_keeps_the_original_signer_and_authorizations :
    (payment point origin template).signer = template.request.signer ∧
    (payment point origin template).consents = template.request.consents ∧
    (payment point origin template).purpose = template.request.purpose ∧
    (payment point origin template).gates = template.request.gates := ⟨rfl,rfl,rfl,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt
