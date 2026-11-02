import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Responsibility.Work

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

/-- A public table transformation. It never inspects the actual hidden history. -/
def policy (cap : Nat) (raw : code.Policy) : code.Policy := fun key inside =>
  if (raw key inside).length ≤ cap then raw key inside else []

def schedule (cap : Nat) (raw : Residual.Schedule code) : Residual.Schedule code :=
  fun n => (raw n).map (policy code cap)

def Supported (raw : code.Policy) : Prop :=
  ∀ key inside, ∀ request ∈ raw key inside, request ∈ code.actions

theorem every_normalized_cell_is_in_the_generated_catalogue (cap : Nat) (raw : code.Policy)
    (supported : Supported code raw) (key : code.Key) (inside : key ∈ code.keys) :
    policy code cap raw key inside ∈ words code.actions cap := by
  unfold policy
  split
  · exact (mem_words_iff _ _ _).mpr ⟨by assumption,supported key inside⟩
  · exact (mem_words_iff _ _ _).mpr ⟨by simp,by simp⟩

theorem every_normalized_raw_table_is_finitely_enumerated (cap : Nat) (raw : code.Policy)
    (supported : Supported code raw) :
    policy code cap raw ∈ List.pi code.keys (fun _ => words code.actions cap) :=
  (List.mem_pi _ _).mpr (every_normalized_cell_is_in_the_generated_catalogue code cap raw supported)

private theorem action_unchanged (cap : Nat) (raw : code.Policy) (site : Fin code.sites)
    (signal : Fin code.signals) (bounded : (code.action raw site signal).length ≤ cap) :
    code.action (policy code cap raw) site signal = code.action raw site signal := by
  unfold Code.action at *
  split at * <;> simp_all [policy]

private theorem step_unchanged (cap : Nat) (raw : code.Policy) (state : State code)
    (event : Event Party Good Port Technology Instrument code.sites)
    (bounded : (stepLocal code raw state event).word.length ≤ cap) :
    stepLocal code (policy code cap raw) state event = stepLocal code raw state event := by
  cases event with
  | adversary => rfl
  | send => rfl
  | deliver => rfl
  | activate site =>
    have same := action_unchanged code cap raw site (state.frame.inbox site) bounded
    simp only [stepLocal,Code.step,List.nil_append,same]

/-- Only the word which the original execution actually activates must fit. -/
theorem one_step_preserves_the_entire_state (cap : Nat) (raw : Option code.Policy)
    (input : Input code) (state : State code)
    (bounded : (word code raw input state).length ≤ cap) :
    advance code (raw.map (policy code cap)) input state = advance code raw input state := by
  cases raw with
  | none => rfl
  | some raw =>
    cases chosen : decision code input state with
    | none => simp only [advance,word,Option.map_some,chosen]
    | some event =>
      have localBound : (stepLocal code raw state event.val).word.length ≤ cap := by
        simpa only [word,chosen] using bounded
      have same := step_unchanged code cap raw state event.val localBound
      simp only [advance,word,Option.map_some,chosen,same]

/-- Same adaptive opponent, complete state, packet addresses, mailboxes and history. -/
theorem all_actual_prefixes_are_preserved (cap : Nat) (raw : Residual.Schedule code)
    (input : Input code) (seed : State code) (horizon : Nat)
    (bounded : ∀ n < horizon,
      (word code (raw n) input (Residual.run code raw input seed n)).length ≤ cap) :
    ∀ n ≤ horizon,
      Residual.run code (schedule code cap raw) input seed n = Residual.run code raw input seed n := by
  intro n inside
  induction n with
  | zero => rfl
  | succ n ih =>
    change advance code ((raw n).map (policy code cap)) input
      (Residual.run code (schedule code cap raw) input seed n) = _
    rw [ih (by omega)]
    exact one_step_preserves_the_entire_state code cap (raw n) input _ (bounded n (by omega))

def cost (raw : Residual.Schedule code) (input : Input code) (seed : State code)
    (horizon : Nat) (party : Party) (good : Good) : ℚ :=
  ((List.range horizon).map fun n =>
    let state := Residual.run code raw input seed n
    code.law.totalDebit (code.law.rawItems state.current (word code (raw n) input state)) party good).sum

theorem each_actual_debit_is_in_the_original_total (raw : Residual.Schedule code)
    (input : Input code) (seed : State code) (horizon : Nat) (party : Party) (good : Good)
    (n : Nat) (inside : n < horizon) :
    let state := Residual.run code raw input seed n
    code.law.totalDebit (code.law.rawItems state.current (word code (raw n) input state)) party good ≤
      cost code raw input seed horizon party good := by
  apply List.single_le_sum
  · intro amount member
    obtain ⟨offset,_,rfl⟩ := List.mem_map.mp member
    exact Institutions.Capitalism.Universal.Source.Material.total_nonnegative _ _ (fun item _ =>
      Institutions.Capitalism.Universal.Source.Material.paid_nonnegative code.law item party good)
  · exact List.mem_map.mpr ⟨n,List.mem_range.mpr inside,rfl⟩

theorem original_paid_cost_generates_all_actual_word_bounds
    (raw : Residual.Schedule code) (input : Input code) (seed : State code) (horizon : Nat)
    (party : Party) (good : Good) (floor : Gross.Floor code.law party good code.actions)
    (budget : ℚ) (affordable : cost code raw input seed horizon party good ≤ budget)
    (supported : ∀ n < horizon, ∀ request ∈
      word code (raw n) input (Residual.run code raw input seed n), request ∈ code.actions)
    (legal : ∀ n < horizon, ∀ item ∈ code.law.rawItems
      (Residual.run code raw input seed n).current
      (word code (raw n) input (Residual.run code raw input seed n)),
      code.law.Valid item.before item.request) :
    ∀ n < horizon,
      (word code (raw n) input (Residual.run code raw input seed n)).length ≤ floor.cap budget := by
  intro n inside
  have generated := floor.every_cost_bounded_raw_word_is_enumerated budget
    (Residual.run code raw input seed n).current _ (supported n inside) (legal n inside)
    ((each_actual_debit_is_in_the_original_total code raw input seed horizon party good n inside).trans affordable)
  exact ((mem_words_iff _ _ _).mp generated).1

/-- No old actionLimit membership, length bound or equal-trajectory premise. -/
theorem source_paid_normalization_preserves_every_complete_prefix
    (raw : Residual.Schedule code) (input : Input code) (seed : State code) (horizon : Nat)
    (party : Party) (good : Good) (floor : Gross.Floor code.law party good code.actions)
    (budget : ℚ) (affordable : cost code raw input seed horizon party good ≤ budget)
    (supported : ∀ n < horizon, ∀ request ∈
      word code (raw n) input (Residual.run code raw input seed n), request ∈ code.actions)
    (legal : ∀ n < horizon, ∀ item ∈ code.law.rawItems
      (Residual.run code raw input seed n).current
      (word code (raw n) input (Residual.run code raw input seed n)),
      code.law.Valid item.before item.request) :
    ∀ n ≤ horizon,
      Residual.run code (schedule code (floor.cap budget) raw) input seed n =
        Residual.run code raw input seed n :=
  all_actual_prefixes_are_preserved code (floor.cap budget) raw input seed horizon
    (original_paid_cost_generates_all_actual_word_bounds code raw input seed horizon party good floor budget affordable supported legal)

/-- External attempts, including refused and arbitrarily long ones, are untouched. -/
def WorkBound (cap : Nat) (raw : Option code.Policy) (input : Input code) (state : State code) : Prop :=
  match raw, decision code input state with
  | some raw, some event => match event.val with
    | .activate site => (code.action raw site (state.frame.inbox site)).length ≤ cap
    | _ => True
  | _, _ => True

def LawfulWork (raw : Option code.Policy) (input : Input code) (state : State code) : Prop :=
  match raw, decision code input state with
  | some raw, some event => match event.val with
    | .activate site =>
      (∀ request ∈ code.action raw site (state.frame.inbox site), request ∈ code.actions) ∧
      (∀ item ∈ code.law.rawItems state.current (code.action raw site (state.frame.inbox site)),
        code.law.Valid item.before item.request)
    | _ => True
  | _, _ => True

theorem one_step_preserves_all_external_attempts (cap : Nat) (raw : Option code.Policy)
    (input : Input code) (state : State code) (bounded : WorkBound code cap raw input state) :
    advance code (raw.map (policy code cap)) input state = advance code raw input state := by
  cases raw with
  | none => rfl
  | some raw =>
    cases chosen : decision code input state with
    | none => simp only [advance,word,Option.map_some,chosen]
    | some event =>
      have same : stepLocal code (policy code cap raw) state event.val = stepLocal code raw state event.val := by
        rcases event with ⟨event,inside⟩
        cases event with
        | adversary => rfl
        | send => rfl
        | deliver => rfl
        | activate site =>
          have bound : (code.action raw site (state.frame.inbox site)).length ≤ cap := by
            simpa only [WorkBound,chosen] using bounded
          exact step_unchanged code cap raw state (.activate site) bound
      simp only [advance,word,Option.map_some,chosen,same]

theorem all_prefixes_preserve_external_attempts (cap : Nat) (raw : Residual.Schedule code)
    (input : Input code) (seed : State code) (horizon : Nat)
    (bounded : ∀ n < horizon, WorkBound code cap (raw n) input (Residual.run code raw input seed n)) :
    ∀ n ≤ horizon,
      Residual.run code (schedule code cap raw) input seed n = Residual.run code raw input seed n := by
  intro n inside
  induction n with
  | zero => rfl
  | succ n ih =>
    change advance code ((raw n).map (policy code cap)) input
      (Residual.run code (schedule code cap raw) input seed n) = _
    rw [ih (by omega)]
    exact one_step_preserves_all_external_attempts code cap (raw n) input _ (bounded n (by omega))

theorem gross_budget_bounds_only_local_work
    (raw : Residual.Schedule code) (input : Input code) (seed : State code) (horizon : Nat)
    (party : Party) (good : Good) (floor : Gross.Floor code.law party good code.actions)
    (budget : ℚ) (affordable : cost code raw input seed horizon party good ≤ budget)
    (legal : ∀ n < horizon, LawfulWork code (raw n) input (Residual.run code raw input seed n)) :
    ∀ n < horizon, WorkBound code (floor.cap budget) (raw n) input (Residual.run code raw input seed n) := by
  intro n inside
  let state := Residual.run code raw input seed n
  have lawful := legal n inside
  change WorkBound code (floor.cap budget) (raw n) input state
  change LawfulWork code (raw n) input state at lawful
  have debit : code.law.totalDebit (code.law.rawItems state.current (word code (raw n) input state)) party good ≤ budget := (each_actual_debit_is_in_the_original_total code raw input seed horizon party good n inside).trans affordable
  cases control : raw n with
  | none => simp only [WorkBound]
  | some rawPolicy =>
    cases chosen : decision code input state with
    | none => simp only [WorkBound,chosen]
    | some event =>
      rcases event with ⟨event,member⟩
      cases event with
      | adversary => simp only [WorkBound,chosen]
      | send => simp only [WorkBound,chosen]
      | deliver => simp only [WorkBound,chosen]
      | activate site =>
        have original : word code (raw n) input state = code.action rawPolicy site (state.frame.inbox site) := by
          simp only [word,control,chosen,stepLocal,Code.step,List.nil_append]
        simp only [WorkBound,chosen]
        change (code.action rawPolicy site (state.frame.inbox site)).length ≤ floor.cap budget
        have paid : (∀ request ∈ code.action rawPolicy site (state.frame.inbox site), request ∈ code.actions) ∧
            (∀ item ∈ code.law.rawItems state.current (code.action rawPolicy site (state.frame.inbox site)),
              code.law.Valid item.before item.request) := by
          simpa only [LawfulWork,control,chosen] using lawful
        rw [original] at debit
        exact ((mem_words_iff _ _ _).mp
          (floor.every_cost_bounded_raw_word_is_enumerated budget state.current _ paid.1 paid.2 debit)).1

theorem paid_normalization_keeps_every_adaptive_external_deviation
    (raw : Residual.Schedule code) (input : Input code) (seed : State code) (horizon : Nat)
    (party : Party) (good : Good) (floor : Gross.Floor code.law party good code.actions)
    (budget : ℚ) (affordable : cost code raw input seed horizon party good ≤ budget)
    (legal : ∀ n < horizon, LawfulWork code (raw n) input (Residual.run code raw input seed n)) :
    ∀ n ≤ horizon,
      Residual.run code (schedule code (floor.cap budget) raw) input seed n =
        Residual.run code raw input seed n :=
  all_prefixes_preserve_external_attempts code (floor.cap budget) raw input seed horizon
    (gross_budget_bounds_only_local_work code raw input seed horizon party good floor budget affordable legal)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization
