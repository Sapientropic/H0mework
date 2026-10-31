import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit

open Institutions.Capitalism.Universal.Source.Program

def receipts (programme : OutstandingSource Party Good Port Technology Unit) (count : Nat) :=
  (List.range count).flatMap fun ordinal => programme.seed.law.rawItems
    (programme.frameAt ordinal).raw (programme.frameWord ordinal (programme.frameAt ordinal))

theorem receipt_balance (programme : OutstandingSource Party Good Port Technology Unit)
    (count : Nat) (actor : Party) (good : Good) :
    (programme.frameAt count).raw.stock actor good + programme.seed.law.totalDebit (receipts programme count) actor good =
      programme.seed.initial.stock actor good + programme.seed.law.totalCredit (receipts programme count) actor good := by
  induction count with
  | zero => simp [receipts, OutstandingSource.frameAt, RawLaw.totalDebit, RawLaw.totalCredit]
  | succ count ih =>
    have step := programme.seed.law.actual_next_material_balance (programme.frameAt count).raw
      (programme.frameWord count (programme.frameAt count)) actor good
    change (programme.frameAt (count + 1)).raw.stock actor good + _ = _ at step
    have split : receipts programme (count + 1) = receipts programme count ++
        programme.seed.law.rawItems (programme.frameAt count).raw
          (programme.frameWord count (programme.frameAt count)) := by
      simp only [receipts, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [split]
    simp only [RawLaw.totalDebit, RawLaw.totalCredit, List.map_append, List.sum_append] at *
    linarith

theorem receipts_are_the_generated_machine (count : Nat) :
    receipts source count = (List.range count).flatMap fun ordinal =>
      law.rawItems (frameAt ordinal).raw (wordAt ordinal (frameAt ordinal)) := by
  apply List.flatMap_congr
  intro ordinal _inside
  change law.rawItems _ _ = _
  rw [← raw_current_frame, ← (source.canonical_frame ordinal).2,
    actual_word_is_machine, current_is_generated_machine]

def programme (shared : Bool) := if shared then source else Cell.source

theorem all_actual_flow_addresses_are_below_six (shared : Bool) :
    ∀ item ∈ receipts (programme shared) 11, ∀ entry ∈
      law.actualDebit item.before item.request ++ law.actualCredit item.before item.request,
      entry.1.1 < 6 := by
  cases shared
  · decide +kernel
  · change ∀ item ∈ receipts source 11, _
    rw [receipts_are_the_generated_machine]
    decide +kernel

private theorem outside_flow_zero (shared : Bool) (actor : Party) (outside : 6 ≤ actor)
    (item : ExecutionItem Party Good Port Technology Unit) (inside : item ∈ receipts (programme shared) 11)
    (good : Good) :
    flowAt (law.actualDebit item.before item.request) actor good = 0 ∧
      flowAt (law.actualCredit item.before item.request) actor good = 0 := by
  have zero (flow : Flow Party Good) (bounded : ∀ entry ∈ flow, entry.1.1 < 6) : flowAt flow actor good = 0 := by
    unfold flowAt amount
    apply List.sum_eq_zero
    intro value member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    have different : entry.1 ≠ (actor, good) := by
      intro same
      have address := congrArg Prod.fst same
      have bound := bounded entry present
      have tooSmall : actor < 6 := by simpa only [address] using bound
      exact Nat.not_lt_of_ge outside tooSmall
    simp only [if_neg different]
  exact ⟨zero _ (fun entry member => all_actual_flow_addresses_are_below_six shared item inside entry
    (List.mem_append_left _ member)), zero _ (fun entry member =>
      all_actual_flow_addresses_are_below_six shared item inside entry (List.mem_append_right _ member))⟩

theorem outside_totals_zero (shared : Bool) (actor : Party) (outside : 6 ≤ actor) (good : Good) :
    law.totalDebit (receipts (programme shared) 11) actor good = 0 ∧
      law.totalCredit (receipts (programme shared) 11) actor good = 0 := by
  have debit : law.totalDebit (receipts (programme shared) 11) actor good = 0 := by
    unfold RawLaw.totalDebit
    apply List.sum_eq_zero
    intro value member
    obtain ⟨item, inside, rfl⟩ := List.mem_map.mp member
    exact (outside_flow_zero shared actor outside item inside good).1
  have credit : law.totalCredit (receipts (programme shared) 11) actor good = 0 := by
    unfold RawLaw.totalCredit
    apply List.sum_eq_zero
    intro value member
    obtain ⟨item, inside, rfl⟩ := List.mem_map.mp member
    exact (outside_flow_zero shared actor outside item inside good).2
  exact ⟨debit, credit⟩

theorem outside_inventory_zero (shared : Bool) (actor : Party) (outside : 6 ≤ actor) (good : Good) :
    ((programme shared).frameAt 11).raw.stock actor good = 0 := by
  have balance := receipt_balance (programme shared) 11 actor good
  have debit := (outside_totals_zero shared actor outside good).1
  have credit := (outside_totals_zero shared actor outside good).2
  have sameLaw : (programme shared).seed.law = law := by cases shared <;> rfl
  have sameInitial : (programme shared).seed.initial = initial := by cases shared <;> rfl
  rw [sameLaw, sameInitial, debit, credit] at balance
  have zero : initial.stock actor good = 0 := by
    have a : actor ≠ 0 := by intro same; subst actor; norm_num at outside
    have b : actor ≠ 1 := by intro same; subst actor; norm_num at outside
    have c : actor ≠ 2 := by intro same; subst actor; norm_num at outside
    have d : actor ≠ 3 := by intro same; subst actor; norm_num at outside
    simp [initial, a, b, c, d]
  linarith

private theorem zero_at_execution_cuts (current : Current) (word : List RequestAt)
    (index : Nat) (actor : Party) (zero : ∀ good, current.stock actor good = 0)
    (silent : ∀ item ∈ (law.execute current index word).items, ∀ good,
      flowAt (law.actualDebit item.before item.request) actor good = 0 ∧
      flowAt (law.actualCredit item.before item.request) actor good = 0) :
    (∀ good, (law.execute current index word).final.stock actor good = 0) ∧
      ∀ item ∈ (law.execute current index word).items, ∀ good,
        item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0 := by
  induction word generalizing current index with
  | nil => exact ⟨zero, by simp [RawLaw.execute]⟩
  | cons request rest ih =>
    have head := silent ⟨index, current, request⟩ List.mem_cons_self
    have nextZero (good : Good) : (law.step current request).stock actor good = 0 := by
      have balance := law.material_step_balance current request actor good
      rw [(head good).1, (head good).2, zero good] at balance
      linarith
    have tail := ih (law.step current request) (index + 1) nextZero
      (fun item inside good => silent item (List.mem_cons_of_mem _ inside) good)
    refine ⟨tail.1, ?_⟩
    intro item inside good
    simp only [RawLaw.execute, List.mem_cons] at inside
    rcases inside with rfl | later
    · exact ⟨zero good, nextZero good⟩
    · exact tail.2 item later good

theorem outside_at_every_cut (shared : Bool) (actor : Party) (outside : 6 ≤ actor) :
    ∀ item ∈ receipts (programme shared) 11, ∀ good,
      item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0 := by
  have sameLaw : (programme shared).seed.law = law := by cases shared <;> rfl
  have sameInitial : (programme shared).seed.initial = initial := by cases shared <;> rfl
  have loop (count : Nat) (bounded : count ≤ 11) :
      (∀ good, ((programme shared).frameAt count).raw.stock actor good = 0) ∧
        ∀ item ∈ receipts (programme shared) count, ∀ good,
          item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0 := by
    induction count with
    | zero =>
      refine ⟨?_, by simp [receipts]⟩
      intro good
      change (programme shared).seed.initial.stock actor good = 0
      rw [sameInitial]
      have a : actor ≠ 0 := by intro same; subst actor; norm_num at outside
      have b : actor ≠ 1 := by intro same; subst actor; norm_num at outside
      have c : actor ≠ 2 := by intro same; subst actor; norm_num at outside
      have d : actor ≠ 3 := by intro same; subst actor; norm_num at outside
      simp [initial, a, b, c, d]
    | succ count ih =>
      have previous := ih (by omega)
      have step := zero_at_execution_cuts ((programme shared).frameAt count).raw
        ((programme shared).frameWord count ((programme shared).frameAt count)) 0 actor previous.1 (by
          intro item inside good
          apply outside_flow_zero shared actor outside item _ good
          apply List.mem_flatMap.mpr
          refine ⟨count, List.mem_range.mpr (by omega), ?_⟩
          simpa only [sameLaw, RawLaw.rawItems] using inside)
      refine ⟨?_, ?_⟩
      · intro good
        change ((programme shared).seed.law.next _ _).stock actor good = 0
        rw [sameLaw]
        exact step.1 good
      · intro item inside good
        have split : receipts (programme shared) (count + 1) = receipts (programme shared) count ++
            (programme shared).seed.law.rawItems ((programme shared).frameAt count).raw
              ((programme shared).frameWord count ((programme shared).frameAt count)) := by
          simp only [receipts, List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [split, List.mem_append] at inside
        rcases inside with old | fresh
        · exact previous.2 item old good
        · apply step.2 item _ good
          simpa only [sameLaw, RawLaw.rawItems] using fresh
  exact (loop 11 (by decide)).2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
