import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Effects

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback

open Institutions.Capitalism.Universal.Source.Program

def receipts (count : Nat) := (List.range count).flatMap fun ordinal =>
  law.rawItems (source.frameAt ordinal).raw (source.frameWord ordinal (source.frameAt ordinal))

theorem receipts_succ (count : Nat) : receipts (count + 1) = receipts count ++
    law.rawItems (source.frameAt count).raw (source.frameWord count (source.frameAt count)) := by
  simp [receipts, List.range_succ, List.flatMap_append]

theorem cumulative_material_balance (count : Nat) (actor : Party) (good : Good) :
    (source.frameAt count).raw.stock actor good + law.totalDebit (receipts count) actor good =
      initial.stock actor good + law.totalCredit (receipts count) actor good := by
  induction count with
  | zero => simpa [receipts, OutstandingSource.frameAt, RawLaw.totalDebit, RawLaw.totalCredit] using
      (show source.seed.initial.stock actor good = initial.stock actor good from rfl)
  | succ count prior =>
      have step := every_actual_boundary_balances count actor good
      rw [receipts_succ]
      simp only [RawLaw.totalDebit, RawLaw.totalCredit, List.map_append, List.sum_append] at ⊢
      simp only [RawLaw.totalDebit, RawLaw.totalCredit] at prior step
      linarith

def stockFromReceipts (count : Nat) (actor : Party) (good : Good) : ℚ :=
  initial.stock actor good - law.totalDebit (receipts count) actor good + law.totalCredit (receipts count) actor good

theorem receipt_consumer_matches_every_actor (count : Nat) (actor : Party) (good : Good) :
    stockFromReceipts count actor good = (source.currentAt count).stock actor good := by
  rw [raw_current_frame]
  unfold stockFromReceipts
  linarith [cumulative_material_balance count actor good]

def participants (count : Nat) : List Party :=
  [0, 1, 2, 3] ++ (receipts count).flatMap fun item =>
    (law.actualDebit item.before item.request ++ law.actualCredit item.before item.request).map (fun entry => entry.1.1)

theorem every_actual_flow_party_is_registered (count : Nat)
    (item : ExecutionItem Party Good Port Technology Unit) (member : item ∈ receipts count)
    (entry : (Party × Good) × ℚ)
    (inside : entry ∈ law.actualDebit item.before item.request ++ law.actualCredit item.before item.request) :
    entry.1.1 ∈ participants count :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨item, member, List.mem_map.mpr ⟨entry, inside, rfl⟩⟩)

private theorem outside_flow_is_zero (actors : List Party) (actor : Party) (good : Good)
    (outside : actor ∉ actors) (flow : Flow Party Good)
    (registered : ∀ entry ∈ flow, entry.1.1 ∈ actors) : flowAt flow actor good = 0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro quantity member
  obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp member
  have different : entry.1 ≠ (actor, good) := by
    intro same
    apply outside
    have location : entry.1.1 = actor := congrArg Prod.fst same
    exact location ▸ registered entry inside
  simp only [if_neg different]

theorem outside_generated_support_has_zero_stock (count : Nat) (actor : Party) (good : Good)
    (outside : actor ∉ participants count) : (source.currentAt count).stock actor good = 0 := by
  have debitZero (item : ExecutionItem Party Good Port Technology Unit) (member : item ∈ receipts count) :
      flowAt (law.actualDebit item.before item.request) actor good = 0 :=
    outside_flow_is_zero _ actor good outside _ (fun entry inside =>
      every_actual_flow_party_is_registered count item member entry (List.mem_append_left _ inside))
  have creditZero (item : ExecutionItem Party Good Port Technology Unit) (member : item ∈ receipts count) :
      flowAt (law.actualCredit item.before item.request) actor good = 0 :=
    outside_flow_is_zero _ actor good outside _ (fun entry inside =>
      every_actual_flow_party_is_registered count item member entry (List.mem_append_right _ inside))
  have totalDebitZero : law.totalDebit (receipts count) actor good = 0 := by
    unfold RawLaw.totalDebit
    apply List.sum_eq_zero
    intro quantity member
    obtain ⟨item, inside, rfl⟩ := List.mem_map.mp member
    exact debitZero item inside
  have totalCreditZero : law.totalCredit (receipts count) actor good = 0 := by
    unfold RawLaw.totalCredit
    apply List.sum_eq_zero
    intro quantity member
    obtain ⟨item, inside, rfl⟩ := List.mem_map.mp member
    exact creditZero item inside
  have notOriginal : actor ∉ ([0, 1, 2, 3] : List Party) :=
    fun member => outside (List.mem_append_left _ member)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notOriginal
  have initialZero : initial.stock actor good = 0 := by
    simp [initial, notOriginal.1, notOriginal.2.1, notOriginal.2.2.1, notOriginal.2.2.2]
  rw [raw_current_frame]
  have balance := cumulative_material_balance count actor good
  rw [totalDebitZero, totalCreditZero, initialZero] at balance
  linarith

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback
