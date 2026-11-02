import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

private theorem prior_step_legal (raw : code.Policy)
    (current : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (event : Event Party Good Port Technology Instrument code.sites)
    (legal : (code.step raw current frame event).localLegal = true) : frame.localLegal = true := by
  cases event with
  | adversary => exact legal
  | send => exact (Bool.and_eq_true_iff.mp legal).1
  | activate => exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp legal).1).1
  | deliver address =>
    cases packet : frame.sent[address]? with
    | none => simpa only [Code.step,packet] using legal
    | some packet =>
      simp only [Code.step,packet] at legal
      exact (Bool.and_eq_true_iff.mp legal).1

private theorem prior_advance_legal (raw : Option code.Policy) (input : Input code) (state : State code)
    (legal : (advance code raw input state).frame.localLegal = true) : state.frame.localLegal = true := by
  cases raw with
  | none => exact legal
  | some raw =>
    cases chosen : decision code input state with
    | none => simpa only [advance,chosen] using legal
    | some event =>
      have after : (stepLocal code raw state event.val).localLegal = true := by
        simpa only [advance,chosen] using legal
      exact prior_step_legal code raw state.current {state.frame with word := []} event.val after

private theorem action_supported (raw : code.Policy) (supported : Supported code raw)
    (site : Fin code.sites) (signal : Fin code.signals) :
    ∀ request ∈ code.action raw site signal, request ∈ code.actions := by
  unfold Code.action
  split
  · exact supported _ _
  · simp

private theorem lawful_advance_work (raw : Option code.Policy) (input : Input code) (state : State code)
    (supported : ∀ policy, raw = some policy → Supported code policy)
    (legal : (advance code raw input state).frame.localLegal = true) : LawfulWork code raw input state := by
  cases raw with
  | none => trivial
  | some raw =>
    cases chosen : decision code input state with
    | none => simp only [LawfulWork,chosen]
    | some event =>
      rcases event with ⟨event,member⟩
      cases event with
      | adversary => simp only [LawfulWork,chosen]
      | send => simp only [LawfulWork,chosen]
      | deliver => simp only [LawfulWork,chosen]
      | activate site =>
        simp only [LawfulWork,chosen]
        refine ⟨action_supported code raw (supported raw rfl) site _,?_⟩
        simp only [advance,chosen,stepLocal,Code.step] at legal
        have paid : decide (∀ item ∈ code.law.rawItems state.current
            (code.action raw site (state.frame.inbox site)), code.law.Valid item.before item.request) = true :=
          (Bool.and_eq_true_iff.mp legal).2
        exact of_decide_eq_true paid

theorem original_final_legality_generates_every_local_work_obligation
    (raw : Residual.Schedule code) (input : Input code) (seed : State code) (horizon : Nat)
    (supported : ∀ n < horizon, ∀ policy, raw n = some policy → Supported code policy)
    (legal : (Residual.run code raw input seed horizon).frame.localLegal = true) :
    ∀ n < horizon, LawfulWork code (raw n) input (Residual.run code raw input seed n) := by
  have prior (m : Nat) (n : Nat) (inside : n ≤ m)
      (legal : (Residual.run code raw input seed m).frame.localLegal = true) :
      (Residual.run code raw input seed n).frame.localLegal = true := by
    induction m generalizing n with
    | zero =>
      have same : n = 0 := by omega
      subst n
      exact legal
    | succ m ih =>
      by_cases same : n = m+1
      · subst n;exact legal
      · exact ih n (by omega) (prior_advance_legal code (raw m) input _ legal)
  intro n inside
  exact lawful_advance_work code (raw n) input _ (supported n inside)
    (prior horizon (n+1) (by omega) legal)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization
