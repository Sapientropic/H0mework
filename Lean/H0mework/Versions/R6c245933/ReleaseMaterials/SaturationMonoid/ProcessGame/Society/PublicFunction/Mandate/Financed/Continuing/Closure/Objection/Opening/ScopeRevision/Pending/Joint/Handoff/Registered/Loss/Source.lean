import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Source
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} {authority : ScopeRevision.Ready old}
  {originInputs : List (List Action)} {inventory : Pending.Joint.Inventory authority originInputs}
  {fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs} {original : List Action}

structure Request (cursor : Cursor authority inventory fresh original) where
  private mk ::
  index : Fin cursor.book.length
  chosen : selected cursor.book = some index
  order : Raw.Reparation.Order (cursor.book.get index).original (cursor.book.get index).account
  selectedOrder : Raw.Reparation.selected (cursor.book.get index).original (cursor.book.get index).account = some order

def request (cursor : Cursor authority inventory fresh original) (index : Fin cursor.book.length)
    (chosen : selected cursor.book = some index) : Request cursor :=
  match found : Raw.Reparation.selected (cursor.book.get index).original (cursor.book.get index).account with
  | some order => ⟨index,chosen,order,found⟩
  | none => False.elim (by
      have member : index ∈ pending cursor.book := List.mem_of_mem_head? chosen
      have nonempty := (List.mem_filter.mp member).2
      have empty := List.head?_eq_none_iff.mp found
      rw [empty] at nonempty
      cases nonempty)

inductive Assessment (cursor : Cursor authority inventory fresh original) where
  | private quiet (noPending : selected cursor.book = none)
  | private allocated (request : Request cursor)
      (valid : (law fresh).Valid cursor.before (request.order.request (law fresh) cursor.before))
      (positive : 0 < (cursor.book.get request.index).change (law fresh) cursor.before request.order.key)
  | private refused (request : Request cursor)
      (denied : ¬ (law fresh).Valid cursor.before (request.order.request (law fresh) cursor.before))
      (remaining : ∀ key, ((cursor.book.get request.index).advance (law fresh) cursor.before).account.remaining key =
        (cursor.book.get request.index).account.remaining key)

def Assessment.isAllocated {cursor : Cursor authority inventory fresh original} : Assessment cursor → Bool
  | .allocated .. => true
  | _ => false

def Assessment.isRefused {cursor : Cursor authority inventory fresh original} : Assessment cursor → Bool
  | .refused .. => true
  | _ => false

def assess (cursor : Cursor authority inventory fresh original) : Assessment cursor :=
  match chosen : selected cursor.book with
  | none => .quiet chosen
  | some index =>
      let req := request cursor index chosen
      if valid : (law fresh).Valid cursor.before (req.order.request (law fresh) cursor.before) then
        .allocated req valid (by
          have actual := (Raw.Reparation.a_lawful_attempt_pays_part_of_the_original_cell_or_is_an_actual_refusal
            (cursor.book.get req.index).original (cursor.book.get req.index).account (law fresh) cursor.before req.order req.selectedOrder).resolve_right
            (fun bad => bad.1 valid)
          simpa only [Entry.change,Entry.advance,Raw.Reparation.advance,add_sub_cancel_left] using actual.2)
      else .refused req valid (by
        intro key
        exact (Raw.Reparation.a_refused_request_cannot_pay_any_cell _ _ _ _ req.order req.selectedOrder valid key).2)

variable (cursor : Cursor authority inventory fresh original) (actor : Bool)
def epoch := World.Epoch.ofFresh fresh
def choiceWord (choice : World.Input.Choice) := World.Input.candidate (epoch (fresh := fresh)) .revision cursor.before choice
def Available (choice : World.Input.Choice) : Prop :=
  World.Input.Legal (epoch (fresh := fresh)) .revision cursor.before choice ∧
    World.Input.Event.SelfDeviation.LocalWord actor (choiceWord cursor choice)
instance (choice : World.Input.Choice) : Decidable (Available cursor actor choice) := by unfold Available; infer_instance

structure Reply where
  private mk ::
  choice : World.Input.Choice
  generated : choice ∈ World.Input.menu (epoch (fresh := fresh)) .revision cursor.before
  legal : Available cursor actor choice

def reply? : Option (Reply cursor actor) :=
  match chosen : (World.Input.menu (epoch (fresh := fresh)) .revision cursor.before).find? (fun choice => decide (Available cursor actor choice)) with
  | some choice => some ⟨choice,List.mem_of_find?_eq_some chosen,of_decide_eq_true (List.find?_some (p := fun choice => decide (Available cursor actor choice)) chosen)⟩
  | none => none

theorem absent_reply_is_an_exact_current_law_or_signature_failure (absent : reply? cursor actor = none) :
    ∀ choice ∈ World.Input.menu (epoch (fresh := fresh)) .revision cursor.before, ¬ Available cursor actor choice := by
  unfold reply? at absent
  split at absent
  · cases absent
  · rename_i denied
    intro choice member accepted
    have failed := List.find?_eq_none.mp denied choice member
    rw [decide_eq_true accepted] at failed
    exact failed rfl

def reaction : Cursor authority inventory fresh original :=
  match reply? cursor actor with
  | none => cursor
  | some reply => cursor.accept (choiceWord cursor reply.choice)

def reactionRun : (Financial.Family.process Pending.Joint.Finance.sources).Run cursor.state.finance.current
    (reaction cursor actor).state.finance.current := by
  unfold reaction
  split
  · exact .nil
  · exact Continuation.financialRun _ _

def advance : Cursor authority inventory fresh original :=
  match assess cursor with
  | .refused req .. => reaction cursor.next req.order.key.1
  | .quiet .. | .allocated .. => cursor.next

def advanceRun : (Financial.Family.process Pending.Joint.Finance.sources).Run cursor.state.finance.current
    (advance cursor).state.finance.current := by
  unfold advance
  split
  · exact cursor.financialRun.concatRuns _ (reactionRun _ _)
  · exact cursor.financialRun
  · exact cursor.financialRun

theorem refused_request_drives_its_own_actual_followup (req : Request cursor) (denied remaining)
    (checked : assess cursor = .refused req denied remaining) :
    advance cursor = reaction cursor.next req.order.key.1 := by simp only [advance,checked]

def run : Nat → Cursor authority inventory fresh original
  | 0 => cursor
  | count+1 => advance (run count)
def runFinancial : (count : Nat) → (Financial.Family.process Pending.Joint.Finance.sources).Run cursor.state.finance.current
    (run cursor count).state.finance.current
  | 0 => .nil
  | count+1 => (runFinancial count).concatRuns _ (advanceRun (run cursor count))

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Source
