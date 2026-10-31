import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} (inventory : Inventory ready originInputs)

structure Slice (position : Repayment.Position Bool Unit) where
  private mk ::
  before : Current
  front : List Action
  suffix : List Action
  decomposition : emit ready inventory = front ++ Repayment.Portfolio.Repair.word (epochLaw ready) position before ++ suffix
  actual_before : ((epochLaw ready).execute (current ready inventory.inputs) 0 front).final = before

def slice (index : Fin (positions ready inventory).length) : Slice ready inventory (positions ready inventory)[index] :=
  let located := Repayment.Portfolio.locate (epochLaw ready) (positions ready inventory) (afterPrefix ready inventory) index
  { before := located.before
    front := objectionWord ready inventory ++ located.front
    suffix := located.suffix
    decomposition := by
      change objectionWord ready inventory ++ Repayment.Portfolio.word (epochLaw ready) (positions ready inventory) (afterPrefix ready inventory) = _
      rw [located.decomposition]
      simp only [List.append_assoc]
    actual_before := by
      rw [Repayment.Portfolio.execute_append_final]
      exact located.actual_before }

def Slice.response {position : Repayment.Position Bool Unit} (slice : Slice ready inventory position) :=
  Repayment.respond (epochLaw ready) position slice.before

def Slice.orders {position : Repayment.Position Bool Unit} (slice : Slice ready inventory position) :=
  Repayment.Portfolio.Repair.orders (epochLaw ready) position slice.before

theorem Slice.item_is_in_whole_trace {position : Repayment.Position Bool Unit} (slice : Slice ready inventory position)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ (epochLaw ready).rawItems slice.before (Repayment.Portfolio.Repair.word (epochLaw ready) position slice.before)) :
    Repayment.Portfolio.shifted slice.front.length item ∈ (epochLaw ready).rawItems (current ready inventory.inputs) (emit ready inventory) := by
  rw [slice.decomposition]
  unfold RawLaw.rawItems
  rw [(epochLaw ready).execute_append]
  apply List.mem_append_left
  rw [(epochLaw ready).execute_append]
  apply List.mem_append_right
  rw [slice.actual_before, Repayment.Portfolio.execute_reindexed]
  exact List.mem_map.mpr ⟨item, member, rfl⟩

theorem Slice.request_is_in_whole_word {position : Repayment.Position Bool Unit} (slice : Slice ready inventory position)
    (request : Action) (member : request ∈ Repayment.Portfolio.Repair.word (epochLaw ready) position slice.before) :
    request ∈ emit ready inventory := by
  rw [slice.decomposition]
  exact List.mem_append_left _ (List.mem_append_right _ member)

theorem Slice.ready_payment_is_actual {position : Repayment.Position Bool Unit} (slice : Slice ready inventory position)
    (paid : Repayment.Ready (epochLaw ready) position slice.before) :
    ∃ item ∈ (epochLaw ready).rawItems (current ready inventory.inputs) (emit ready inventory),
      item.before = Repayment.readyCurrent (epochLaw ready) position slice.before ∧
      item.request = Repayment.payment (epochLaw ready) position slice.before ∧
      (epochLaw ready).Valid item.before item.request := by
  have positive : 0 < Repayment.balance position slice.before :=
    lt_of_lt_of_le paid.1 (min_le_left _ _)
  obtain ⟨item, member, before, requested, valid⟩ := Repayment.payment_is_an_actual_item (epochLaw ready) position slice.before paid
  have included : item ∈ (epochLaw ready).rawItems slice.before (Repayment.Portfolio.Repair.word (epochLaw ready) position slice.before) := by
    rw [Repayment.Portfolio.Repair.paid_word_is_the_original_candidate _ _ _ positive paid]
    exact member
  exact ⟨Repayment.Portfolio.shifted slice.front.length item, slice.item_is_in_whole_trace ready inventory item included,
    before, requested, valid⟩

theorem Slice.failed_front_and_repair_are_actual {position : Repayment.Position Bool Unit} (slice : Slice ready inventory position)
    (positive : 0 < Repayment.balance position slice.before) (failed : ¬ Repayment.Ready (epochLaw ready) position slice.before)
    (order : Repayment.Portfolio.Repair.Order (epochLaw ready) position slice.before)
    (present : order ∈ slice.orders ready) :
    Repayment.Portfolio.shifted slice.front.length order.failed ∈ (epochLaw ready).rawItems (current ready inventory.inputs) (emit ready inventory) ∧
    ¬ (epochLaw ready).Valid order.failed.before order.failed.request ∧ order.request ∈ emit ready inventory := by
  have actual := Repayment.Portfolio.Repair.every_order_has_a_real_front_refusal (epochLaw ready) position slice.before order positive failed
  exact ⟨slice.item_is_in_whole_trace ready inventory order.failed actual.1, actual.2,
    slice.request_is_in_whole_word ready inventory order.request
      (Repayment.Portfolio.Repair.every_order_is_an_actual_requested_suffix _ _ _ order present positive failed)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement
