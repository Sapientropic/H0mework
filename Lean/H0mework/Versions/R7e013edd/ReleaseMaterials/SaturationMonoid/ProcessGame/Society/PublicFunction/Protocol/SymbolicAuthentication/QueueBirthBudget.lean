import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthBudget
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (origin cursor : Cursor model.source.code)

abbrev final (count : Nat) := EventHistory.execute cursor (QueueBirthSource.stages origin count)
abbrev family := Native.Authority.programme model
abbrev inputs (count : Nat) := Native.Authority.sourceIndex (LocalContentRuntime.native model (final model origin cursor count))
abbrev begin := EventStep.boundary cursor

theorem every_actual_queue_visit_funds_its_final_source_birth_slice (count index : Nat) (inside : index < count) :
    CompletedInventory.openBorn (family model) (inputs model origin cursor count) (begin model cursor + index) ≤
      (QueueBirthSource.row origin cursor index).submitted.length := by
  have row := OriginQueue.row_at_its_actual_index origin cursor QueueBirthSource.protocols count index inside
  have member := List.mem_of_getElem? row
  have budget := NativeBirthWord.every_actual_open_birth_is_funded_by_its_submitted_request_word model cursor
    (QueueBirthSource.stages origin count) (QueueBirthSource.row origin cursor index) member
  have boundary := IncidentChallenge.execution_advances_the_actual_boundary model cursor (QueueBirthSource.stages origin index)
  rw [OriginQueue.executed_stages_are_the_actual_cursor, OriginQueue.stage_count] at boundary
  change EventStep.boundary (OriginQueue.cursorAt origin cursor QueueBirthSource.protocols index) = begin model cursor + index at boundary
  change CompletedInventory.openBorn (family model) (inputs model origin cursor count)
    (EventStep.boundary (OriginQueue.cursorAt origin cursor QueueBirthSource.protocols index)) ≤ _ at budget
  rw [boundary] at budget
  exact budget

theorem the_actual_queue_window_has_a_source_funded_birth_and_residual_rank_bound
    (fits : OriginQueue.baseline origin ≤ (EventStep.seed cursor).past.length) (count : Nat) :
    InventoryBirthBudget.arrivals (family model) (inputs model origin cursor count) (begin model cursor) count +
      QueueBirthSource.rank origin cursor count * QueueBirthSource.cost model.source.code ≤
      QueueBirthSource.rank origin cursor 0 * QueueBirthSource.cost model.source.code := by
  have prefixBound : ∀ index ≤ count,
      InventoryBirthBudget.arrivals (family model) (inputs model origin cursor count) (begin model cursor) index +
        QueueBirthSource.rank origin cursor index * QueueBirthSource.cost model.source.code ≤
        QueueBirthSource.rank origin cursor 0 * QueueBirthSource.cost model.source.code := by
    intro index
    induction index with
    | zero => intro _; simp only [InventoryBirthBudget.arrivals, Nat.zero_add, Nat.le_refl]
    | succ index ih =>
      intro bounded
      have previous := ih (by omega)
      have born := every_actual_queue_visit_funds_its_final_source_birth_slice model origin cursor count index (by omega)
      have paid := QueueBirthSource.every_actual_wait_pays_its_word_from_a_strict_address_decrease origin cursor fits index
      simp only [InventoryBirthBudget.arrivals]
      omega
  exact prefixBound count (Nat.le_refl _)

theorem the_actual_origin_queue_window_has_a_finite_native_arrival_bound
    (fits : OriginQueue.baseline origin ≤ (EventStep.seed cursor).past.length) (count : Nat) :
    InventoryBirthBudget.arrivals (family model) (inputs model origin cursor count) (begin model cursor) count ≤
      (QueueScheduler.admitted model.source.code).card * QueueBirthSource.cost model.source.code := by
  have paid := the_actual_queue_window_has_a_source_funded_birth_and_residual_rank_bound model origin cursor fits count
  have available : QueueBirthSource.rank origin cursor 0 ≤ (QueueScheduler.admitted model.source.code).card :=
    Finset.card_le_card Finset.sdiff_subset
  have finite := Nat.mul_le_mul_right (QueueBirthSource.cost model.source.code) available
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthBudget
