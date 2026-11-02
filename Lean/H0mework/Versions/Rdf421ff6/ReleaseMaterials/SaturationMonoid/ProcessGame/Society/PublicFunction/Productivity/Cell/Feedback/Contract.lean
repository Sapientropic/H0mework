import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Local

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback

open Institutions.Capitalism.Universal.Source.Program

def accountingSilent (request : RequestAt) : Bool :=
  match request.operation with
  | .issue .. | .assign .. | .settle .. => false
  | _ => true

theorem copy_silent (parent child : Party) : (copy parent child).all accountingSilent = true := by
  simp [copy, firstCycle, audit, transfer, production, necessity, maintenance, accountingSilent]

theorem prefix_silent (current : Current) (parent child : Party) :
    (failedPrefix current parent child).all accountingSilent = true := by
  unfold failedPrefix
  cases attemptCopy current parent child with
  | paid _ => rfl
  | blocked failed original refused =>
      apply List.all_eq_true.mpr
      intro request inside
      exact List.all_eq_true.mp (copy_silent parent child) request (List.mem_of_mem_take inside)

theorem gather_good_silent (current : Current) (recipient : Party) (good : Good)
    (required : ℚ) (suppliers : List Party) :
    (gatherGood current recipient good required suppliers).all accountingSilent = true := by
  induction suppliers generalizing current with
  | nil => rfl
  | cons supplier rest ih =>
      dsimp only [gatherGood]
      split <;> simp [transfer, accountingSilent, ih]

theorem gather_silent (current : Current) (recipient : Party) (needs : Bundle Good) :
    (gather current recipient needs).all accountingSilent = true := by
  induction needs generalizing current with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨good, required⟩
      simp only [gather, List.all_append, gather_good_silent, ih, Bool.true_and]

theorem recycle_silent (current : Current) (recipient : Party) :
    (recycle current recipient).all accountingSilent = true := by
  unfold recycle
  split <;> simp [transfer, production, accountingSilent]

theorem repair_silent (current : Current) (parent child : Party) :
    (repairWord current parent child).all accountingSilent = true := by
  simp only [repairWord, List.all_append, prefix_silent, gather_silent, recycle_silent, Bool.true_and]

theorem response_silent (current : Current) (started : 10 < current.round) :
    (respond current).word.all accountingSilent = true := by
  unfold respond
  rw [if_neg (by omega : ¬ current.round ≤ 10)]
  split
  · exact copy_silent _ _
  · exact repair_silent _ _ _

theorem silent_step_keeps_claims (current : Current) (request : RequestAt)
    (silent : accountingSilent request = true) : (law.step current request).claims = current.claims := by
  unfold RawLaw.step
  split
  · cases operation : request.operation <;>
      simp_all [accountingSilent, RawLaw.paidStep, RawLaw.nextClaims]
  · rfl

theorem silent_execution_keeps_claims (current : Current) (word : RawEvent Party Good Port Technology Unit)
    (silent : word.all accountingSilent = true) (index : Nat) :
    (law.execute current index word).final.claims = current.claims := by
  induction word generalizing current index with
  | nil => rfl
  | cons request rest ih =>
      have flags : accountingSilent request = true ∧ rest.all accountingSilent = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using silent
      exact (ih (law.step current request) flags.2 (index + 1)).trans
        (silent_step_keeps_claims current request flags.1)

theorem response_keeps_all_financial_positions (current : Current) (started : 10 < current.round) :
    (law.next current (respond current).word).claims = current.claims :=
  silent_execution_keeps_claims current _ (response_silent current started) 0

theorem addresses_are_distinct (current : Current) :
    parent current < child current ∧ child current ≠ 3 := by
  unfold child
  exact ⟨lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _),
    ne_of_gt (lt_of_lt_of_le (by decide : (3 : Nat) < 6) (Nat.le_max_left _ _))⟩

theorem copy_item_survives_its_prefix (current : Current) (parent child : Party)
    (item : ExecutionItem Party Good Port Technology Unit)
    (original : item ∈ law.rawItems current (copy parent child)) :
    item ∈ law.rawItems current ((copy parent child).take (item.index + 1)) := by
  simp only [copy, firstCycle, List.cons_append, List.nil_append, RawLaw.rawItems,
    RawLaw.execute, List.mem_cons, List.not_mem_nil, or_false] at original
  rcases original with rfl | rfl | rfl | rfl | rfl <;>
    simp [copy, firstCycle, RawLaw.rawItems, RawLaw.execute]

theorem rejected_candidate_is_in_repair_execution (current : Current) (parent child : Party)
    (failed : ExecutionItem Party Good Port Technology Unit)
    (original : failed ∈ law.rawItems current (copy parent child))
    (refused : ¬ law.Valid failed.before failed.request)
    (selected : attemptCopy current parent child = .blocked failed original refused) :
    failed ∈ law.rawItems current (repairWord current parent child) := by
  have member : failed ∈ law.rawItems current (failedPrefix current parent child) := by
    unfold failedPrefix
    rw [selected]
    exact copy_item_survives_its_prefix current parent child failed original
  let first := failedPrefix current parent child
  let supplies := gather (law.execute current 0 first).final parent budget
  let regeneration := recycle (law.execute current 0 (first ++ supplies)).final parent
  change failed ∈ (law.execute current 0 ((first ++ supplies) ++ regeneration)).items
  rw [law.execute_append]
  apply List.mem_append_left
  rw [law.execute_append]
  exact List.mem_append_left _ member

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback
