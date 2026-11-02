import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Accounting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit

open Institutions.Capitalism.Universal.Source.Program

def actors (count : Nat) : List Party := (Feedback.participants count).eraseDups

theorem actor_mem (count : Nat) (actor : Party) : actor ∈ actors count ↔ actor ∈ Feedback.participants count := by
  simp [actors]

theorem receipt_member (count ordinal : Nat) (before : ordinal < count)
    (item : ExecutionItem Party Good Port Technology Unit)
    (inside : item ∈ law.rawItems (source.frameAt ordinal).raw
      (source.frameWord ordinal (source.frameAt ordinal))) : item ∈ Feedback.receipts count :=
  List.mem_flatMap.mpr ⟨ordinal, List.mem_range.mpr before, inside⟩

private theorem outside_flow_zero (count : Nat) (actor : Party) (good : Good)
    (outside : actor ∉ actors count) (item : ExecutionItem Party Good Port Technology Unit)
    (member : item ∈ Feedback.receipts count) :
    flowAt (law.actualDebit item.before item.request) actor good = 0 ∧
    flowAt (law.actualCredit item.before item.request) actor good = 0 := by
  have unregistered : actor ∉ Feedback.participants count := fun present => outside ((actor_mem _ _).mpr present)
  have zero (flow : Flow Party Good)
      (registered : ∀ entry ∈ flow, entry.1.1 ∈ Feedback.participants count) : flowAt flow actor good = 0 := by
    unfold flowAt amount
    apply List.sum_eq_zero
    intro quantity present
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp present
    have different : entry.1 ≠ (actor, good) := by
      intro same
      have location : entry.1.1 = actor := congrArg Prod.fst same
      exact unregistered (location ▸ registered entry inside)
    simp only [if_neg different]
  exact ⟨zero _ (fun entry inside => Feedback.every_actual_flow_party_is_registered count item member entry
      (List.mem_append_left _ inside)),
    zero _ (fun entry inside => Feedback.every_actual_flow_party_is_registered count item member entry
      (List.mem_append_right _ inside))⟩

private theorem zero_at_every_execution_cut (current : Current)
    (word : RawEvent Party Good Port Technology Unit) (index : Nat) (actor : Party)
    (zero : ∀ good, current.stock actor good = 0)
    (silent : ∀ item ∈ (law.execute current index word).items, ∀ good,
      flowAt (law.actualDebit item.before item.request) actor good = 0 ∧
      flowAt (law.actualCredit item.before item.request) actor good = 0) :
    (∀ good, (law.execute current index word).final.stock actor good = 0) ∧
    ∀ item ∈ (law.execute current index word).items, ∀ good,
      item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0 := by
  induction word generalizing current index with
  | nil => exact ⟨zero, by simp [RawLaw.execute]⟩
  | cons request rest ih =>
      have headSilent := silent ⟨index, current, request⟩ (by simp [RawLaw.execute])
      have nextZero (good : Good) : (law.step current request).stock actor good = 0 := by
        have balance := law.material_step_balance current request actor good
        rw [(headSilent good).1, (headSilent good).2, zero good] at balance
        linarith
      have tail := ih (law.step current request) (index + 1) nextZero (by
        intro item inside good
        exact silent item (List.mem_cons_of_mem _ inside) good)
      refine ⟨tail.1, ?_⟩
      intro item inside good
      simp only [RawLaw.execute, List.mem_cons] at inside
      rcases inside with rfl | later
      · exact ⟨zero good, nextZero good⟩
      · exact tail.2 item later good

theorem every_actual_cut_has_complete_inventory (count : Nat)
    (item : ExecutionItem Party Good Port Technology Unit) (member : item ∈ Feedback.receipts count)
    (actor : Party) (outside : actor ∉ actors count) (good : Good) :
    item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0 := by
  have notOriginal : actor ∉ ([0, 1, 2, 3] : List Party) := fun inside =>
    outside ((actor_mem _ _).mpr (List.mem_append_left _ inside))
  have initialZero (kind : Good) : initial.stock actor kind = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notOriginal
    simp [initial, notOriginal.1, notOriginal.2.1, notOriginal.2.2.1, notOriginal.2.2.2]
  have frameZero : ∀ ordinal ≤ count, ∀ kind, (source.frameAt ordinal).raw.stock actor kind = 0 := by
    intro ordinal bound
    induction ordinal with
    | zero => exact initialZero
    | succ ordinal ih =>
        exact (zero_at_every_execution_cut (source.frameAt ordinal).raw
          (source.frameWord ordinal (source.frameAt ordinal)) 0 actor (ih (by omega)) (by
            intro entry inside kind
            exact outside_flow_zero count actor kind outside entry
              (receipt_member count ordinal (by omega) entry inside))).1
  obtain ⟨ordinal, earlier, inside⟩ := List.mem_flatMap.mp member
  have bound := List.mem_range.mp earlier
  exact (zero_at_every_execution_cut _ _ 0 actor (frameZero ordinal (by omega)) (by
    intro entry present kind
    exact outside_flow_zero count actor kind outside entry (receipt_member count ordinal bound entry present))).2
      item inside good

def needsFloor (current : Current) (actor : Party) : Prop :=
  actor ∈ source.seed.task.slots.map ServiceSlot.bearer ∨ 0 < current.stock actor .seed

instance (current : Current) (actor : Party) : Decidable (needsFloor current actor) := by
  unfold needsFloor; infer_instance

def livingFloor (current : Current) (actor : Party) : Prop :=
  needsFloor current actor → 1 ≤ current.stock actor .life ∧ 1 ≤ current.stock actor .spare

instance (current : Current) (actor : Party) : Decidable (livingFloor current actor) := by
  unfold livingFloor; infer_instance

def checkCuts (items : List (ExecutionItem Party Good Port Technology Unit)) (parties : List Party) : Bool :=
  items.all fun item => parties.all fun actor =>
    decide (livingFloor item.before actor ∧ livingFloor (law.step item.before item.request) actor)

def floorCheck (count : Nat) : Bool := checkCuts (Feedback.receipts count) (actors count)

structure CutViolation (items : List (ExecutionItem Party Good Port Technology Unit)) (parties : List Party) where
  item : ExecutionItem Party Good Port Technology Unit
  original_item : item ∈ items
  actor : Party
  registered : actor ∈ parties
  broken : ¬ (livingFloor item.before actor ∧ livingFloor (law.step item.before item.request) actor)

def violations (items : List (ExecutionItem Party Good Port Technology Unit)) (parties : List Party) :
    List (CutViolation items parties) :=
  items.attach.flatMap fun item => parties.attach.filterMap fun actor =>
    if broken : ¬ (livingFloor item.val.before actor.val ∧
        livingFloor (law.step item.val.before item.val.request) actor.val) then
      some ⟨item.val, item.property, actor.val, actor.property, broken⟩
    else none

theorem violation_is_enumerated (items : List (ExecutionItem Party Good Port Technology Unit))
    (parties : List Party) (violation : CutViolation items parties) : violation ∈ violations items parties := by
  unfold violations
  apply List.mem_flatMap.mpr
  refine ⟨⟨violation.item, violation.original_item⟩, List.mem_attach _ _, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨⟨violation.actor, violation.registered⟩, List.mem_attach _ _, ?_⟩
  rw [dif_pos violation.broken]

theorem failed_floor_check_has_concrete_cut (items : List (ExecutionItem Party Good Port Technology Unit))
    (parties : List Party) (failed : checkCuts items parties = false) :
    (violations items parties).isEmpty = false := by
  apply List.isEmpty_eq_false_iff.mpr
  intro empty
  have accepted : checkCuts items parties = true := by
    apply List.all_eq_true.mpr
    intro item inside
    apply List.all_eq_true.mpr
    intro actor registered
    apply decide_eq_true
    by_contra broken
    have member := violation_is_enumerated items parties ⟨item, inside, actor, registered, broken⟩
    rw [empty] at member
    cases member
  rw [accepted] at failed
  cases failed

theorem floor_check_covers_every_participant (count : Nat) (accepted : floorCheck count = true)
    (item : ExecutionItem Party Good Port Technology Unit) (member : item ∈ Feedback.receipts count)
    (actor : Party) : livingFloor item.before actor ∧ livingFloor (law.step item.before item.request) actor := by
  by_cases inside : actor ∈ actors count
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp accepted item member) actor inside)
  · have stockZero := every_actual_cut_has_complete_inventory count item member actor inside
    have original : actor ∉ source.seed.task.slots.map ServiceSlot.bearer := by
      intro present
      have initialActor : actor ∈ ([0, 1, 2, 3] : List Party) := by
        have originalActor : actor = 0 ∨ actor = 1 ∨ actor = 2 := by simpa [source, task] using present
        rcases originalActor with rfl | rfl | rfl <;> decide
      exact inside ((actor_mem _ _).mpr (List.mem_append_left _ initialActor))
    constructor <;> intro responsibility
    · rcases responsibility with origin | seed
      · exact False.elim (original origin)
      · rw [(stockZero .seed).1] at seed; exact False.elim (lt_irrefl _ seed)
    · rcases responsibility with origin | seed
      · exact False.elim (original origin)
      · rw [(stockZero .seed).2] at seed; exact False.elim (lt_irrefl _ seed)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit
