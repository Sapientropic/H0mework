import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Portfolio.Repair

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Portfolio

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

def word : List (Position Party Instrument) → RawCurrent Party Good Technology Instrument →
    RawEvent Party Good Port Technology Instrument
  | [], _ => []
  | position :: rest, current =>
      let first := Repair.word law position current
      first ++ word rest (law.execute current 0 first).final

theorem execute_final_index (current : RawCurrent Party Good Technology Instrument)
    (body : RawEvent Party Good Port Technology Instrument) (first second : Nat) :
    (law.execute current first body).final = (law.execute current second body).final := by
  induction body generalizing current first second with
  | nil => rfl
  | cons request tail ih => exact ih (law.step current request) (first + 1) (second + 1)

theorem execute_append_final (current : RawCurrent Party Good Technology Instrument)
    (first second : RawEvent Party Good Port Technology Instrument) :
    (law.execute current 0 (first ++ second)).final =
      (law.execute (law.execute current 0 first).final 0 second).final := by
  rw [law.execute_append]
  exact execute_final_index law _ _ _ _

def shifted (offset : Nat) (item : ExecutionItem Party Good Port Technology Instrument) :=
  {item with index := item.index + offset}

theorem execute_reindexed (current : RawCurrent Party Good Technology Instrument)
    (body : RawEvent Party Good Port Technology Instrument) (start offset : Nat) :
    (law.execute current (start + offset) body).items =
      ((law.execute current start body).items.map (shifted offset)) := by
  induction body generalizing current start with
  | nil => rfl
  | cons request tail ih =>
      change _ :: (law.execute (law.step current request) (start + offset + 1) tail).items =
        _ :: ((law.execute (law.step current request) (start + 1) tail).items.map (shifted offset))
      rw [show start + offset + 1 = (start + 1) + offset by omega, ih]
      rfl

structure Slice (positions : List (Position Party Instrument))
    (current : RawCurrent Party Good Technology Instrument) (position : Position Party Instrument) where
  private mk ::
  before : RawCurrent Party Good Technology Instrument
  front : RawEvent Party Good Port Technology Instrument
  suffix : RawEvent Party Good Port Technology Instrument
  decomposition : word law positions current = front ++ Repair.word law position before ++ suffix
  actual_before : (law.execute current 0 front).final = before

def locate (positions : List (Position Party Instrument))
    (current : RawCurrent Party Good Technology Instrument) (index : Fin positions.length) :
    Slice law positions current positions[index] := by
  induction positions generalizing current with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
      refine Fin.cases ?_ (fun smaller => ?_) index
      · exact ⟨current, [], word law rest (law.execute current 0 (Repair.word law first current)).final, rfl, rfl⟩
      · let prior := Repair.word law first current
        let next := (law.execute current 0 prior).final
        let found := ih next smaller
        refine ⟨found.before, prior ++ found.front, found.suffix, ?_, ?_⟩
        · change prior ++ word law rest next =
            (prior ++ found.front) ++ Repair.word law rest[smaller] found.before ++ found.suffix
          rw [found.decomposition]
          simp only [List.append_assoc]
        · rw [execute_append_final]
          exact found.actual_before

theorem every_listed_position_has_an_actual_slice
    (positions : List (Position Party Instrument)) (current : RawCurrent Party Good Technology Instrument)
    (position : Position Party Instrument) (member : position ∈ positions) :
    Nonempty (Slice law positions current position) := by
  obtain ⟨index, inside, same⟩ := List.mem_iff_getElem.mp member
  cases same
  exact ⟨locate law positions current ⟨index, inside⟩⟩

theorem Slice.item_is_in_the_whole_trace
    {positions : List (Position Party Instrument)} {current : RawCurrent Party Good Technology Instrument}
    {position : Position Party Instrument} (slice : Slice law positions current position)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (member : item ∈ law.rawItems slice.before (Repair.word law position slice.before)) :
    shifted slice.front.length item ∈ law.rawItems current (word law positions current) := by
  rw [slice.decomposition]
  unfold RawLaw.rawItems
  rw [law.execute_append]
  apply List.mem_append_left
  rw [law.execute_append]
  change shifted slice.front.length item ∈ (law.execute current 0 slice.front).items ++
    (law.execute (law.execute current 0 slice.front).final (0 + slice.front.length)
      (Repair.word law position slice.before)).items
  apply List.mem_append_right
  rw [slice.actual_before, execute_reindexed]
  exact List.mem_map.mpr ⟨item, member, rfl⟩

theorem Slice.request_is_in_the_whole_word
    {positions : List (Position Party Instrument)} {current : RawCurrent Party Good Technology Instrument}
    {position : Position Party Instrument} (slice : Slice law positions current position)
    (request : Request Party Good Port Technology Instrument)
    (member : request ∈ Repair.word law position slice.before) :
    request ∈ word law positions current := by
  rw [slice.decomposition]
  exact List.mem_append_left _ (List.mem_append_right _ member)

theorem Slice.failed_candidate_and_generated_repair_are_actual
    {positions : List (Position Party Instrument)} {current : RawCurrent Party Good Technology Instrument}
    {position : Position Party Instrument} (slice : Slice law positions current position)
    (positive : 0 < balance position slice.before) (failed : ¬ Ready law position slice.before)
    (order : Repair.Order law position slice.before) (present : order ∈ Repair.orders law position slice.before) :
    shifted slice.front.length order.failed ∈ law.rawItems current (word law positions current) ∧
    ¬ law.Valid (shifted slice.front.length order.failed).before (shifted slice.front.length order.failed).request ∧
    order.request ∈ word law positions current := by
  have original := Repair.every_order_has_a_real_front_refusal law position slice.before order positive failed
  exact ⟨slice.item_is_in_the_whole_trace law order.failed original.1, original.2,
    slice.request_is_in_the_whole_word law order.request
      (Repair.every_order_is_an_actual_requested_suffix law position slice.before order present positive failed)⟩

theorem Slice.ready_payment_is_in_the_whole_trace
    {positions : List (Position Party Instrument)} {current : RawCurrent Party Good Technology Instrument}
    {position : Position Party Instrument} (slice : Slice law positions current position)
    (ready : Ready law position slice.before) :
    ∃ item ∈ law.rawItems current (word law positions current),
      item.before = readyCurrent law position slice.before ∧
      item.request = payment law position slice.before ∧ law.Valid item.before item.request := by
  have positive : 0 < balance position slice.before :=
    lt_of_lt_of_le ready.1 (show quantity law position slice.before ≤ balance position slice.before from min_le_left _ _)
  obtain ⟨item, inside, before, requested, accepted⟩ := payment_is_an_actual_item law position slice.before ready
  have inWord : item ∈ law.rawItems slice.before (Repair.word law position slice.before) := by
    rw [Repair.paid_word_is_the_original_candidate law position slice.before positive ready]
    exact inside
  exact ⟨shifted slice.front.length item, slice.item_is_in_the_whole_trace law item inWord, before, requested, accepted⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Portfolio
