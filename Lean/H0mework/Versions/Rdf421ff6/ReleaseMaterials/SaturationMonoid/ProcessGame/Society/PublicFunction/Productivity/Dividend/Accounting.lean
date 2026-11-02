import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend

open Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication Root Exit

theorem first_programme_is_authorized (n : Nat) (shared : Bool) :
    ∀ item ∈ (execution n shared 1).interpreted.items,
      (law n).Valid item.before item.request := by
  change ∀ item ∈ ((law n).execute (currentAt n shared 1) 0 (execution n shared 1).submitted).items, _
  rw [first_current, first_word]
  apply ((law n).accepted_retime (time_independent n) (initial n) 1 1 0 (route n shared)).mpr
  cases shared
  · exact exclusive_accepted n
  · exact public_accepted n

/-- The task fixes beneficiaries, whole bundles and a common source window. -/
def task (n : Nat) : PublicTaskSpec Bool Bool where
  slots := [⟨true, [(true, (n : ℚ) + 1)], .necessity⟩,
    ⟨false, [(false, 1)], .maintenance⟩]
  earliest := 1
  deadline := 2
  demand := ⟨⟨false, [(false, 1)], .maintenance⟩, by simp, (false, 1), by simp, by norm_num⟩

theorem same_task_paid_in_the_same_window (n : Nat) (shared : Bool) :
    ServiceAdequate (law n) (currentAt n shared 1) (task n) (execution n shared 1).submitted := by
  refine ⟨?_, ?_, ?_⟩
  · rw [first_current]; norm_num [task, RawCurrent.retime]
  · change ((law n).next (currentAt n shared 1) (execution n shared 1).submitted).clock ≤ 2
    change (execution n shared 1).after.clock ≤ 2
    rw [actual_next, task_current]; norm_num [RawCurrent.retime]
  · intro slot inside
    have paid : Necessity.AllNeedsPaid (law n) (initial n) [false, true] (route n shared) := by
      cases shared
      · exact exclusive_paid n
      · exact public_paid n
    rw [first_current, first_word]
    simp only [task, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact Replay.bundlePaid n (initial n) 1 1 _ true _ .necessity
        (paid true (by simp)).1
    · exact Replay.bundlePaid n (initial n) 1 1 _ false _ .maintenance
        (paid false (by simp)).2

def taskDebit (n : Nat) (shared party good : Bool) : ℚ :=
  (law n).totalDebit (execution n shared 1).interpreted.items party good

def extraDebit (n : Nat) (shared party good : Bool) : ℚ :=
  (law n).totalDebit (execution n shared 2).interpreted.items party good

private theorem debit_as_raw (n : Nat) (shared : Bool) (party good : Bool) :
    (law n).totalDebit ((law n).rawItems (initial n) (route n shared)) party good =
      (((law n).rawItems (initial n) (route n shared)).map fun item =>
        flowAt ((law n).debit item.before item.request) party good).sum := by
  unfold RawLaw.totalDebit
  congr 1
  apply List.map_congr_left
  intro item inside
  have valid : (law n).Valid item.before item.request := by
    cases shared
    · exact exclusive_accepted n item inside
    · exact public_accepted n item inside
  rw [RawLaw.actualDebit, if_pos valid]

/-- All parties and all physical goods are accounted for; no free valuation
or unpriced cost category participates in this difference. -/
theorem complete_task_debits (n : Nat) (shared party good : Bool) :
    taskDebit n shared party good =
      if party then (if good then (n : ℚ) + 1 else 0)
      else if good then (n : ℚ) + 1 else if shared then 3 else (n : ℚ) + 4 := by
  change (law n).totalDebit
    ((law n).execute (currentAt n shared 1) 0 (execution n shared 1).submitted).items party good = _
  rw [first_current, first_word, Replay.totalDebit]
  change (law n).totalDebit ((law n).rawItems (initial n) (route n shared)) party good = _
  rw [debit_as_raw]
  cases shared
  · simp only [route, Bool.false_eq_true, ↓reduceIte, RawLaw.rawItems, exclusive_execution]
    cases party <;> cases good <;>
      simp [RawLaw.debit, produce, deliver, consume, maintain, law, initial, state, flowAt, amount, locate]; ring
  · simp only [route, ↓reduceIte, RawLaw.rawItems, public_execution]
    cases party <;> cases good <;>
      simp [RawLaw.debit, produce, deliver, consume, maintain, openAccess, law, initial, state, flowAt, amount, locate]; ring

theorem complete_task_credits (n : Nat) (shared party good : Bool) :
    (law n).totalCredit (execution n shared 1).interpreted.items party good =
      if good then (n : ℚ) + 1 else 0 := by
  have balance := (law n).actual_next_material_balance (currentAt n shared 1)
    (execution n shared 1).submitted party good
  change (execution n shared 1).after.stock party good + taskDebit n shared party good =
    (currentAt n shared 1).stock party good +
      (law n).totalCredit (execution n shared 1).interpreted.items party good at balance
  rw [actual_next, task_current, first_current, complete_task_debits] at balance
  cases shared <;> cases party <;> cases good <;>
    simp only [initial, state, RawCurrent.retime, ↓reduceIte, Bool.false_eq_true] at * <;> linarith

theorem no_reinvestment_credit (n : Nat) (shared party good : Bool) :
    (law n).totalCredit (execution n shared 2).interpreted.items party good = 0 := by
  unfold RawLaw.totalCredit
  apply List.sum_eq_zero
  intro value inside
  obtain ⟨item, member, same⟩ := List.mem_map.mp inside
  rw [← same]
  have facts := every_reinvestment_cut_is_paid_and_keeps_the_reserve n shared item member
  rw [RawLaw.actualCredit, if_pos facts.1, facts.2.2.2]
  simp [RawLaw.credit, maintain, flowAt, amount]

theorem complete_extra_debits (n : Nat) (shared party good : Bool) :
    extraDebit n shared party good =
      if shared && !party && !good then (n : ℚ) + 1 else 0 := by
  have balance := (law n).actual_next_material_balance (currentAt n shared 2)
    (execution n shared 2).submitted party good
  change (execution n shared 2).after.stock party good + extraDebit n shared party good =
    (currentAt n shared 2).stock party good +
      (law n).totalCredit (execution n shared 2).interpreted.items party good at balance
  rw [actual_next, reinvested_current, task_current, no_reinvestment_credit] at balance
  cases shared <;> cases party <;> cases good <;>
    simp only [state, RawCurrent.retime, ↓reduceIte, Bool.false_eq_true, Bool.and_self,
      Bool.and_false, Bool.false_and, Bool.not_false, Bool.not_true] at * <;> linarith

/-- A physical dividend, in units of fuel. It is not a welfare-weighted score. -/
def dividend (n : Nat) : ℚ := taskDebit n false false false - taskDebit n true false false

theorem exact_strict_dividend_and_actual_payment (n : Nat) :
    dividend n = (n : ℚ) + 1 ∧ 0 < dividend n ∧
      extraDebit n true false false - extraDebit n false false false = dividend n ∧
      (currentAt n true 3).stock = (currentAt n false 3).stock ∧
      (∀ shared instrument debtor holder, (currentAt n shared 3).claims instrument debtor holder = 0) ∧
      (currentAt n true 3).clock = 3 ∧ (currentAt n false 3).clock = 3 := by
  have gap : dividend n = (n : ℚ) + 1 := by
    simp only [dividend, complete_task_debits, Bool.false_eq_true, ↓reduceIte]
    ring
  refine ⟨gap, by rw [gap]; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · rw [complete_extra_debits, complete_extra_debits, gap]; norm_num
  · rw [reinvested_current, reinvested_current]; rfl
  · intro shared instrument debtor holder
    rw [reinvested_current]; rfl
  · rw [reinvested_current]; rfl
  · rw [reinvested_current]; rfl

/-- The reserve difference and its later spending are the same dividend.
Adding them as independent benefits would count one physical unit twice. -/
theorem saved_fuel_equals_spent_dividend (n : Nat) :
    (currentAt n true 2).stock false false - (currentAt n false 2).stock false false = dividend n ∧
      taskDebit n true false false + extraDebit n true false false =
        taskDebit n false false false + extraDebit n false false false := by
  rw [(exact_strict_dividend_and_actual_payment n).1, task_current, task_current]
  constructor
  · change (n : ℚ) + 2 - 1 = (n : ℚ) + 1
    ring
  · simp only [complete_task_debits, complete_extra_debits]
    norm_num
    ring

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend
