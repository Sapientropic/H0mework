import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Accounting

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Access

open Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication Root Exit

private theorem copy_valid (n : Nat) : (law n).Valid (state 1 0 0 true) personalCopy := by
  simp [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, NonnegativeBundle,
    flowAt, amount, locate, law, state, personalCopy]
  positivity

private theorem copy_step (n : Nat) :
    (law n).step (state 1 0 0 true) personalCopy = state 1 0 ((n : ℚ) + 1) true := by
  rw [RawLaw.step, if_pos (copy_valid n)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, personalCopy, law,
        state, flowAt, amount, locate]
  all_goals rfl

private theorem consume_valid (n : Nat) :
    (law n).Valid (state 1 0 ((n : ℚ) + 1) true) (consume n) := by
  simp [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, NonnegativeBundle,
    flowAt, amount, locate, law, state, consume]
  positivity

private theorem consume_step (n : Nat) :
    (law n).step (state 1 0 ((n : ℚ) + 1) true) (consume n) = state 1 0 0 true := by
  rw [RawLaw.step, if_pos (consume_valid n)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, consume,
        state, flowAt, amount, locate]
  all_goals rfl

theorem public_execution (n : Nat) :
    (law n).execute (state 1 0 0 true) 0 (candidate n) =
      ⟨state 1 0 0 true, [⟨0, state 1 0 0 true, personalCopy⟩,
        ⟨1, state 1 0 ((n : ℚ) + 1) true, consume n⟩]⟩ := by
  simp only [candidate, RawLaw.execute, copy_step, consume_step]

theorem public_ready (n : Nat) : Ready n (state 1 0 0 true) := by
  unfold Ready
  rw [RawLaw.rawItems, public_execution]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨copy_valid n, consume_valid n⟩

theorem private_refusal (n : Nat) : ¬ (law n).Valid (state 1 0 0 false) personalCopy := by
  simp [RawLaw.Valid, RawLaw.requiredPorts, law, state, personalCopy]

theorem selected_word (n : Nat) (shared : Bool) (clock : ℚ) (round : Nat) :
    (respond n ((state 1 0 0 shared).retime clock round)).word = if shared then candidate n else [] := by
  unfold respond
  cases shared
  · have rejected : ¬ Ready n ((state 1 0 0 false).retime clock round) := by
      intro ready
      have first := ready ⟨0, (state 1 0 0 false).retime clock round, personalCopy⟩
        (by exact List.mem_cons_self)
      exact private_refusal n (((law n).valid_retime (time_independent n) _ _ _ _).mp first)
    rw [dif_neg rejected]
    rfl
  · have ready : Ready n ((state 1 0 0 true).retime clock round) :=
      ((law n).accepted_retime (time_independent n) _ _ _ 0 _).mpr (public_ready n)
    rw [dif_pos ready]
    rfl

private theorem steady_next (n : Nat) (shared : Bool) (clock : ℚ) (round : Nat) (started : 3 ≤ round) :
    (law n).next ((state 1 0 0 shared).retime clock round)
      (dispatch n shared ((state 1 0 0 shared).retime clock round)) =
        (state 1 0 0 shared).retime (clock + 1) (round + 1) := by
  have emitted : dispatch n shared ((state 1 0 0 shared).retime clock round) =
      if shared then candidate n else [] := by
    simp only [dispatch, show ((state 1 0 0 shared).retime clock round).round = round from rfl,
      if_neg (show round ≠ 1 by omega), if_neg (show round ≠ 2 by omega), if_pos started]
    exact selected_word n shared clock round
  rw [emitted]
  simp only [RawLaw.next, (law n).execute_retime (time_independent n)]
  cases shared
  · simp only [Bool.false_eq_true, ↓reduceIte, RawLaw.execute]
    norm_num [RawCurrent.retime, law]
  · simp only [↓reduceIte, public_execution]
    norm_num [RawCurrent.retime, law]

/-- Every later actual word reuses the same opened technique; no new stock,
permission or replenishment is supplied to the source. -/
theorem every_later_current (n : Nat) (shared : Bool) (later : Nat) :
    currentAt n shared (3 + later) = (state 1 0 0 shared).retime (3 + later) (3 + later) := by
  induction later with
  | zero => simpa using reinvested_current n shared
  | succ later ih =>
    rw [show 3 + (later + 1) = (3 + later) + 1 by omega, ← actual_next]
    change (law n).next (currentAt n shared (3 + later)) (execution n shared (3 + later)).submitted = _
    rw [show 3 + later = (2 + later) + 1 by omega, word_from_current]
    rw [show 2 + later + 1 = 3 + later by omega, ih, steady_next n shared _ _ (by omega)]
    congr 1
    push_cast
    ring

theorem every_later_word (n : Nat) (shared : Bool) (later : Nat) :
    (execution n shared (3 + later)).submitted = if shared then candidate n else [] := by
  rw [show 3 + later = (2 + later) + 1 by omega, word_from_current]
  rw [show 2 + later + 1 = 3 + later by omega, every_later_current]
  simp only [dispatch, show ((state 1 0 0 shared).retime (3 + later) (3 + later)).round = 3 + later from rfl,
    if_neg (show 3 + later ≠ 1 by omega), if_neg (show 3 + later ≠ 2 by omega),
    if_pos (show 3 ≤ 3 + later by omega)]
  exact selected_word n shared _ _

def taskAt (n later : Nat) : PublicTaskSpec Bool Bool where
  slots := [⟨true, [(true, (n : ℚ) + 1)], .necessity⟩]
  earliest := 3 + later
  deadline := 4 + later
  demand := ⟨⟨true, [(true, (n : ℚ) + 1)], .necessity⟩, by simp,
    (true, (n : ℚ) + 1), by simp, by positivity⟩

theorem every_later_programme_is_authorized (n : Nat) (shared : Bool) (later : Nat) :
    ∀ item ∈ (execution n shared (3 + later)).interpreted.items,
      (law n).Valid item.before item.request := by
  change ∀ item ∈ ((law n).execute (currentAt n shared (3 + later)) 0
    (execution n shared (3 + later)).submitted).items, _
  rw [every_later_current, every_later_word]
  cases shared
  · simp [RawLaw.execute]
  · exact ((law n).accepted_retime (time_independent n) _ _ _ 0 _).mpr (public_ready n)

theorem every_later_public_service_is_actually_paid (n later : Nat) :
    ServiceAdequate (law n) (currentAt n true (3 + later)) (taskAt n later)
      (execution n true (3 + later)).submitted := by
  refine ⟨?_, ?_, ?_⟩
  · rw [every_later_current]; exact le_rfl
  · change (execution n true (3 + later)).after.clock ≤ (4 : ℚ) + later
    rw [actual_next, show 3 + later + 1 = 3 + (later + 1) by omega, every_later_current]
    change (3 : ℚ) + ↑(later + 1) ≤ 4 + later
    push_cast
    linarith
  · intro slot inside
    simp only [taskAt, List.mem_singleton] at inside
    subst slot
    rw [every_later_current, every_later_word]
    simp only [↓reduceIte]
    apply Replay.bundlePaid
    refine Or.inr ⟨⟨1, state 1 0 ((n : ℚ) + 1) true, consume n⟩, ?_, consume_valid n, ?_⟩
    · rw [RawLaw.rawItems, public_execution]; simp
    · exact ⟨rfl, rfl, rfl⟩

theorem every_later_service_has_zero_fuel_cost (n : Nat) (shared : Bool) (later : Nat) :
    (law n).totalDebit (execution n shared (3 + later)).interpreted.items false false = 0 ∧
      (law n).totalCredit (execution n shared (3 + later)).interpreted.items true true =
        (if shared then (n : ℚ) + 1 else 0) ∧
      (law n).totalDebit (execution n shared (3 + later)).interpreted.items true true =
        if shared then (n : ℚ) + 1 else 0 := by
  change (law n).totalDebit ((law n).execute (currentAt n shared (3 + later)) 0
    (execution n shared (3 + later)).submitted).items false false = 0 ∧ _
  change _ ∧ (law n).totalCredit ((law n).execute (currentAt n shared (3 + later)) 0
    (execution n shared (3 + later)).submitted).items true true = _ ∧
    (law n).totalDebit ((law n).execute (currentAt n shared (3 + later)) 0
      (execution n shared (3 + later)).submitted).items true true = _
  rw [every_later_current, every_later_word, Replay.totalDebit, Replay.totalCredit, Replay.totalDebit]
  cases shared
  · simp [RawLaw.execute, RawLaw.totalDebit, RawLaw.totalCredit]
  · simp only [↓reduceIte, public_execution, RawLaw.totalDebit, RawLaw.totalCredit,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      RawLaw.actualDebit, RawLaw.actualCredit, if_pos (copy_valid n), if_pos (consume_valid n)]
    simp [RawLaw.debit, RawLaw.credit, personalCopy, consume, law, state, flowAt, amount, locate]

theorem every_later_private_attempt_has_an_original_permission_refusal (n later : Nat) :
    let current := currentAt n false (3 + later)
    (⟨0, current, personalCopy⟩ : ExecutionItem Bool Bool (Option Bool) Bool Unit) ∈
      (law n).rawItems current (candidate n) ∧
      ¬ (law n).Valid current personalCopy ∧
      (execution n false (3 + later)).submitted = [] := by
  dsimp only
  refine ⟨List.mem_cons_self, ?_, every_later_word n false later⟩
  rw [every_later_current, (law n).valid_retime (time_independent n)]
  exact private_refusal n

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Access
