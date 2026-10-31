import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Accounting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open Institutions.Capitalism.Universal.Source.Program

private theorem outside_flow_zero (shared : Bool) (actor : Party) (outside : 6 ≤ actor)
    (item : Born.Item) (member : item ∈ receipts shared 25) (good : Good) :
    flowAt (law.actualDebit item.before item.request) actor good = 0 ∧
      flowAt (law.actualCredit item.before item.request) actor good = 0 := by
  have zero (flow : Flow Party Good) (bounded : ∀ entry ∈ flow, entry.1.1 < 6) : flowAt flow actor good = 0 := by
    unfold flowAt amount
    apply List.sum_eq_zero
    intro value present
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp present
    have different : entry.1 ≠ (actor, good) := by
      intro same
      have bound := bounded entry inside
      have equal := congrArg Prod.fst same
      have too_small : actor < 6 := by simpa only [equal] using bound
      exact Nat.not_lt_of_ge outside too_small
    simp only [if_neg different]
  exact ⟨zero _ (fun entry inside => all_actual_flow_addresses_are_bounded shared item member entry
    (List.mem_append_left _ inside)), zero _ (fun entry inside =>
      all_actual_flow_addresses_are_bounded shared item member entry (List.mem_append_right _ inside))⟩

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
    ∀ item ∈ receipts shared 25, ∀ good,
      item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0 := by
  have sameLaw : (source shared).seed.law = law := by cases shared <;> rfl
  have sameInitial : (source shared).seed.initial = initial := by cases shared <;> rfl
  have loop (count : Nat) (bounded : count ≤ 25) :
      (∀ good, ((source shared).frameAt count).raw.stock actor good = 0) ∧
        ∀ item ∈ receipts shared count, ∀ good,
          item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0 := by
    induction count with
    | zero =>
      refine ⟨?_, by simp [receipts, SharedAudit.receipts]⟩
      intro good
      change (source shared).seed.initial.stock actor good = 0
      rw [sameInitial]
      have a : actor ≠ 0 := by intro same; subst actor; norm_num at outside
      have b : actor ≠ 1 := by intro same; subst actor; norm_num at outside
      have c : actor ≠ 2 := by intro same; subst actor; norm_num at outside
      have d : actor ≠ 3 := by intro same; subst actor; norm_num at outside
      simp [initial, a, b, c, d]
    | succ count ih =>
      have previous := ih (by omega)
      have step := zero_at_execution_cuts ((source shared).frameAt count).raw
        ((source shared).frameWord count ((source shared).frameAt count)) 0 actor previous.1 (by
          intro item inside good
          apply outside_flow_zero shared actor outside item _ good
          apply List.mem_flatMap.mpr
          refine ⟨count, List.mem_range.mpr (by omega), ?_⟩
          simpa only [sameLaw, RawLaw.rawItems] using inside)
      refine ⟨?_, ?_⟩
      · intro good
        change ((source shared).seed.law.next _ _).stock actor good = 0
        rw [sameLaw]
        exact step.1 good
      · intro item inside good
        have split : receipts shared (count + 1) = receipts shared count ++
            (source shared).seed.law.rawItems ((source shared).frameAt count).raw
              ((source shared).frameWord count ((source shared).frameAt count)) := by
          simp only [receipts, SharedAudit.receipts, List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [split, List.mem_append] at inside
        rcases inside with old | fresh
        · exact previous.2 item old good
        · apply step.2 item _ good
          simpa only [sameLaw, RawLaw.rawItems] using fresh
  exact (loop 25 (by decide)).2


private def floor (current : Current) (actor : Party) : Prop :=
  (actor < 3 ∨ 0 < current.stock actor .seed) →
    1 ≤ current.stock actor .life ∧ 1 ≤ current.stock actor .spare

private instance (current : Current) (actor : Party) : Decidable (floor current actor) := by
  unfold floor
  infer_instance

private theorem finite_cuts_have_the_floor (shared : Bool) : ∀ item ∈ receipts shared 25, ∀ actor : Fin 6,
    floor item.before actor ∧ floor (law.step item.before item.request) actor := by
  rw [receipt_machine shared 25]
  cases shared <;> decide +kernel

theorem every_actual_cut_keeps_all_original_and_seeded_bearers (shared : Bool) :
    ∀ item ∈ receipts shared 25, ∀ actor : Party,
      ((actor < 3 ∨ 0 < item.before.stock actor .seed) →
        1 ≤ item.before.stock actor .life ∧ 1 ≤ item.before.stock actor .spare) ∧
      ((actor < 3 ∨ 0 < (law.step item.before item.request).stock actor .seed) →
        1 ≤ (law.step item.before item.request).stock actor .life ∧
          1 ≤ (law.step item.before item.request).stock actor .spare) := by
  intro item member actor
  by_cases inside : actor < 6
  · exact finite_cuts_have_the_floor shared item member ⟨actor, inside⟩
  · have outside : 6 ≤ actor := Nat.le_of_not_gt inside
    have zero := outside_at_every_cut shared actor outside item member .seed
    constructor
    · rintro (original | seeded)
      · exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (by decide) outside)) original)
      · rw [zero.1] at seeded; exact False.elim (lt_irrefl _ seeded)
    · rintro (original | seeded)
      · exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (by decide) outside)) original)
      · rw [zero.2] at seeded; exact False.elim (lt_irrefl _ seeded)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
