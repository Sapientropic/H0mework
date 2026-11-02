import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Local

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (point : Cursor code) (origin : Origin point) (template : Template (code := code))

structure Activation where
  site : Fin code.sites
  original : Event.activate site ∈ code.eventAlphabet
  own : code.siteParty site = template.debtor

def activation : Option (Activation template) := code.eventAlphabet.attach.findSome? fun event =>
  match exactEvent : event.val with
  | .activate site => if own : code.siteParty site = template.debtor then
      some ⟨site,exactEvent ▸ event.property,own⟩ else none
  | _ => none

variable (selected : Activation template)

/-- The only new quantity is calculated from the preserved original shares.
The original source law still decides every permission and material debit. -/
def policy : code.Policy := fun key _ =>
  if key.1 = selected.site then word point origin template else []

def environment : Opponent code := fun _ _ _ => some ⟨.activate selected.site,selected.original⟩

abbrev target := Future.target point.source point.entry point.cut (environment template selected)
  [some (policy point origin template selected)]
abbrev targetEntry := Future.takeover point.source point.entry point.cut (environment template selected)

def nextPoint : Cursor code :=
  let next := target point origin template selected
  ⟨next.reference,next.reference_generated,next.history,next.original,next.opponent,next.side,
    targetEntry point template selected,next.feedbackOverrides,point.cut+1,point.ownerStart⟩

theorem the_debt_successor_is_its_actual_original_source :
    (nextPoint point origin template selected).source = target point origin template selected := rfl

abbrev seed := Residual.seed point.source point.entry point.cut
abbrev depth := point.source.history.length+1+point.cut
abbrev execution := (target point origin template selected).actualExecution (depth point)

theorem the_generated_word_is_actually_submitted :
    (execution point origin template selected).submitted =
      if (seed point).remaining = 0 then [] else
        if code.memoryReady ((seed point).frame.inbox selected.site) then word point origin template else [] := by
  change ((target point origin template selected).actualExecution
    (point.source.history.length+1+(point.cut+0))).submitted = _
  rw [Future.future_word_is_actually_submitted point.source point.entry point.cut
    (environment template selected) [some (policy point origin template selected)] rfl 0]
  change Feedback.word code (some (policy point origin template selected))
    ⟨environment template selected,point.entry.budget⟩ (seed point) = _
  by_cases exhausted : (seed point).remaining = 0
  · simp only [Feedback.word,decision,exhausted,if_pos]
  · simp [Feedback.word,decision,exhausted,environment,stepLocal,Code.step,Code.action,policy]

theorem the_full_original_financial_prefix_is_preserved (ordinal : Nat) (earlier : ordinal ≤ arrival point) :
    Native.Coupling.Match code point.source.input (target point origin template selected).input
      (Financial.accountAt point.source.input ordinal)
      (Financial.accountAt (target point origin template selected).input ordinal) :=
  Future.complete_finance_before point.source point.entry point.cut (environment template selected)
    [some (policy point origin template selected)] rfl ordinal earlier

theorem a_cleared_original_share_cannot_charge_any_later_loan
    (cleared : quantity point origin template = 0) :
    (execution point origin template selected).submitted = [] ∧
      ((target point origin template selected).currentAt (depth point+2)).claims =
        ((target point origin template selected).currentAt (depth point+1)).claims := by
  have empty : word point origin template = [] := by simp [word,cleared]
  have emitted := the_generated_word_is_actually_submitted point origin template selected
  simp only [empty,ite_self] at emitted
  refine ⟨emitted,?_⟩
  rw [(target point origin template selected).next_is_actual (depth point),emitted]
  rfl

def actualRefusal : Option {item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument //
    item ∈ code.law.rawItems (execution point origin template selected).before
      (execution point origin template selected).submitted ∧ ¬ code.law.Valid item.before item.request} :=
  match inspect (fun item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument =>
      code.law.Valid item.before item.request)
      (code.law.rawItems (execution point origin template selected).before (execution point origin template selected).submitted) with
  | .accepted _ => none
  | .rejected item original refused => some ⟨item,original,refused⟩

private def actualIndex (index : OldSlot point origin) :
    Fin (Financial.accountAt (target point origin template selected).input origin.val).current.slots.length :=
  ⟨index.val,by
    have count := congrArg List.length (the_full_original_financial_prefix_is_preserved point origin template selected
      origin.val (by have bounded := origin.isLt;omega)).slots
    have lengths : (Financial.accountAt (target point origin template selected).input origin.val).current.slots.length =
        (account point origin).current.slots.length := by
      simpa only [Identity.financeImage,List.length_map] using count
    rw [lengths]
    exact index.isLt⟩

def actualOriginal (index : OldSlot point origin) :=
  (Financial.accountAt (target point origin template selected).input origin.val).current.slots.get
    (actualIndex point origin template selected index)

def actualFollow (index : OldSlot point origin) :=
  Financial.Migration.actual (target point origin template selected).input origin.val
    (arrival point+1-origin.val) index.val (actualOriginal point origin template selected index)
    (List.getElem?_eq_getElem (actualIndex point origin template selected index).isLt)

theorem every_saved_original_slot_has_its_actual_continuation (index : OldSlot point origin) :
    ∃ slot, (Financial.accountAt (target point origin template selected).input
      (origin.val+(arrival point+1-origin.val))).current.slots[index.val]? = some slot ∧
      Nonempty (Financial.Migration.Path (target point origin template selected).input
        (actualOriginal point origin template selected index) slot) :=
  ⟨(actualFollow point origin template selected index).slot,
    (actualFollow point origin template selected index).present,
    ⟨(actualFollow point origin template selected index).path⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt
