import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Regression
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
noncomputable section
abbrev authority := Registered.Regression.authority
abbrev inventory := Registered.Regression.inventory
abbrev fresh := Registered.Regression.fresh

def front : List Action := [⟨false,[],.resource,[],.produce false⟩]
def pair : List Action :=
  let first := (law fresh).execute (start fresh) 0 front |>.final
  let proposal := Mandate.request fresh.scope first false (.propose true)
  [proposal,Mandate.request fresh.scope ((law fresh).step first proposal) true .accept]
def useSurplus : Action := ⟨false,[],.resource,[],.use false [(.service,2)] .external⟩
def denied : Action := ⟨false,[],fresh.scope.service,[fresh.scope.service],.produce false⟩
def original := front ++ pair ++ [useSurplus,denied]
def cursor := Loss.initial authority inventory fresh original

def originalEntry := cursor.book.get ⟨2,by decide +kernel⟩
def afterPayment := cursor.next
def cell (book : Book) : Option (ℚ × ℚ) := book[2]?.map fun entry =>
  (entry.account.paid (false,.service),entry.account.remaining (false,.service))

theorem the_source_selects_the_original_loss_cell : Loss.selected cursor.book = some ⟨2,by decide +kernel⟩ := by
  with_unfolding_all decide +kernel


theorem the_original_occurrence_is_the_actual_start_and_literal_input :
    originalEntry.original = (⟨law fresh,start fresh,original⟩ :
      Raw.Occurrence Bool Good Mandate.Source.Port (State Bool Unit) Unit) := by
  change (⟨law fresh,(Registered.actual authority inventory fresh original).before,
    (Registered.actual authority inventory fresh original).submitted⟩ :
      Raw.Occurrence Bool Good Mandate.Source.Port (State Bool Unit) Unit) = _
  rw [(Registered.literal_input_and_original_in_window_cut authority inventory fresh original).1,
    (Registered.literal_input_and_original_in_window_cut authority inventory fresh original).2]
  rfl

theorem the_original_public_history_generates_its_own_positive_loss :
    Raw.quantity originalEntry.original (false,.service) = 3 ∧ Raw.cohort originalEntry.original = [true] ∧
    originalEntry.account.remaining (false,.service) = 3 := by
  have exactSource := the_original_occurrence_is_the_actual_start_and_literal_input
  constructor
  · rw [exactSource]; decide +kernel
  · constructor
    · rw [exactSource]; decide +kernel
    · change Raw.quantity originalEntry.original (false,.service) = 3
      rw [exactSource]; decide +kernel

theorem actual_material_cut : cursor.before =
    (OutstandingSource.History.replay (source fresh) (Registered.inputs authority inventory fresh original)).frame.raw := rfl

theorem the_actual_source_reparation_pays_all_three :
    cell afterPayment.book = some (3,0) ∧ afterPayment.book.length = 5 ∧
    afterPayment.state.inputs.length = 3 := by
  have literal : Loss.accept cursor.book (law fresh) cursor.before cursor.word =
      Loss.allocate cursor.book (law fresh) cursor.before := if_pos rfl
  have actual : afterPayment.book = Loss.allocate cursor.book (law fresh) cursor.before ++
      [Entry.ofVisit (visit cursor.state cursor.word)] :=
    congrArg (fun book => book ++ [Entry.ofVisit (visit cursor.state cursor.word)]) literal
  constructor
  · calc
      cell afterPayment.book = cell (Loss.allocate cursor.book (law fresh) cursor.before ++
        [Entry.ofVisit (visit cursor.state cursor.word)]) := congrArg cell actual
      _ = some (3,0) := by
        rw [Loss.allocate,the_source_selects_the_original_loss_cell]
        change some ((Raw.Reparation.advance originalEntry.original (Raw.Reparation.initial originalEntry.original)
          (law fresh) cursor.before).paid (false,.service),
          (Raw.Reparation.advance originalEntry.original (Raw.Reparation.initial originalEntry.original)
          (law fresh) cursor.before).remaining (false,.service)) = some (3,0)
        rw [the_original_occurrence_is_the_actual_start_and_literal_input,actual_material_cut]
        with_unfolding_all decide +kernel
  · constructor
    · calc
        afterPayment.book.length = (Loss.allocate cursor.book (law fresh) cursor.before ++
          [Entry.ofVisit (visit cursor.state cursor.word)]).length := congrArg List.length actual
        _ = 5 := by rw [Loss.allocate,the_source_selects_the_original_loss_cell]; decide +kernel
    · with_unfolding_all decide +kernel

def foreignCredit : List Action := [⟨true,[],.resource,[],.transfer true false [(.service,1)]⟩]
def unmatched := cursor.accept foreignCredit

theorem an_actual_unmatched_credit_does_not_discharge_the_original_cell :
    cell unmatched.book = some (0,3) := by
  have generated : cursor.word.head?.map Institutions.Capitalism.Universal.Source.Program.Request.signer = some false := by
    simp only [Loss.Cursor.word,Loss.word,the_source_selects_the_original_loss_cell]
    with_unfolding_all decide +kernel
  have mismatch : foreignCredit ≠ cursor.word := by
    intro same
    have sign := congrArg (fun word => word.head?.map Institutions.Capitalism.Universal.Source.Program.Request.signer) same
    rw [generated] at sign
    change some true = some false at sign
    cases sign
  have same := cursor.unmatched_input_does_not_allocate_old_accounts foreignCredit mismatch
  calc
    cell unmatched.book = cell (cursor.book ++ [Entry.ofVisit (visit cursor.state foreignCredit)]) := congrArg cell same
    _ = some (0,3) := by with_unfolding_all decide +kernel

theorem the_empty_override_adds_its_own_occurrence_without_an_allocation :
    cell (cursor.accept []).book = some (0,3) ∧ (cursor.accept []).book.length = 5 := by
  constructor <;> with_unfolding_all decide +kernel

def materialFailureWord := original ++
  [⟨false,[],.resource,[],.transfer false true [(.feedstock,2)]⟩,
   ⟨true,[],.resource,[],.use true [(.service,1)] .external⟩]
def exhausted := Loss.initial authority inventory fresh materialFailureWord
def repaired := Loss.Source.advance exhausted

theorem the_actual_material_refusal_drives_a_real_self_signed_review :
    (Loss.Source.assess cursor).isAllocated = true ∧
    (Loss.Source.assess exhausted).isRefused = true ∧
    (Loss.Source.reply? exhausted.next false).isSome = true ∧
    repaired.state.inputs.length = exhausted.state.inputs.length + 2 := by
  refine ⟨?_,?_,?_,?_⟩ <;> with_unfolding_all decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Regression
