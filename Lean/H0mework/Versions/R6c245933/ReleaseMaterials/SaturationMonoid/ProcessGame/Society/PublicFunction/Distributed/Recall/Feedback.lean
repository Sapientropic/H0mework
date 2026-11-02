import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual

/-! Actual residual-cut receipts extend prior local memory across arbitrary
supported planner replacements and adaptive opponents. The finite capacity
pays for the complete retained prefix; mailboxes and packets are not reset. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Feedback

open Institutions.Capitalism.Universal.Source.Program
open Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : Code Party Good Port Technology Instrument) (capacity : Nat)

def receipt (control : Option (lift base capacity).Policy)
    (input : Input (lift base capacity)) (state : State (lift base capacity)) (site : Fin base.sites) :
    Option (Notice base) :=
  match control, decision (lift base capacity) input state with
  | some strategy, some event =>
      notice base capacity strategy state.current {state.frame with word := []} event.val site
  | _, _ => none

theorem actual_cut_uses_the_preserved_local_memory
    (control : Option (lift base capacity).Policy)
    (input : Input (lift base capacity)) (state : State (lift base capacity)) (site : Fin base.sites) :
    (advance (lift base capacity) control input state).frame.inbox site =
      match receipt base capacity control input state site with
      | none => state.frame.inbox site
      | some observed => remember base capacity (state.frame.inbox site) observed := by
  cases control with
  | none => rfl
  | some strategy =>
      cases chosen : decision (lift base capacity) input state with
      | none => simp only [advance, receipt, chosen]
      | some event =>
          simp only [advance, receipt, chosen]
          exact actual_step_records_exactly_the_local_notice base capacity strategy state.current
            {state.frame with word := []} event.val site

def observations (schedule : Residual.Schedule (lift base capacity))
    (input : Input (lift base capacity)) (seed : State (lift base capacity)) (site : Fin base.sites) :
    Nat → List (Notice base)
  | 0 => []
  | n + 1 => observations schedule input seed site n ++
      (receipt base capacity (schedule n) input (Residual.run (lift base capacity) schedule input seed n) site).toList

theorem observations_length (schedule : Residual.Schedule (lift base capacity))
    (input : Input (lift base capacity)) (seed : State (lift base capacity)) (site : Fin base.sites) (n : Nat) :
    (observations base capacity schedule input seed site n).length ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      simp only [observations, List.length_append]
      cases receipt base capacity (schedule n) input (Residual.run (lift base capacity) schedule input seed n) site <;>
        simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_singleton] <;> omega

theorem observations_supported (schedule : Residual.Schedule (lift base capacity))
    (supported : ∀ n strategy, schedule n = some strategy → strategy ∈ (lift base capacity).policies)
    (input : Input (lift base capacity)) (seed : State (lift base capacity)) (site : Fin base.sites) (n : Nat) :
    ∀ observed ∈ observations base capacity schedule input seed site n, observed ∈ alphabet base := by
  induction n with
  | zero => simp [observations]
  | succ n ih =>
      intro observed member
      rcases List.mem_append.mp member with old | fresh
      · exact ih observed old
      · unfold receipt at fresh
        cases control : schedule n with
        | none => simp only [control, Option.toList_none, List.not_mem_nil] at fresh
        | some strategy =>
            cases chosen : decision (lift base capacity) input
                (Residual.run (lift base capacity) schedule input seed n) with
            | none => simp only [control, chosen, Option.toList_none, List.not_mem_nil] at fresh
            | some event =>
                simp only [control, chosen] at fresh
                exact notice_is_generated base capacity strategy (supported n strategy control) _ _ event.val site observed fresh

private theorem faithful_prefix (schedule : Residual.Schedule (lift base capacity))
    (input : Input (lift base capacity)) (seed : State (lift base capacity)) (site : Fin base.sites)
    (prior : List (Notice base)) (initial : seed.frame.inbox site = encode base capacity prior) (n : Nat)
    (generated : prior ++ observations base capacity schedule input seed site n ∈ memories base capacity) :
    (Residual.run (lift base capacity) schedule input seed n).frame.inbox site =
      encode base capacity (prior ++ observations base capacity schedule input seed site n) := by
  induction n with
  | zero => simpa only [Residual.run, observations, List.append_nil] using initial
  | succ n ih =>
      have old_generated : prior ++ observations base capacity schedule input seed site n ∈ memories base capacity := by
        obtain ⟨bounded, supported⟩ := (mem_sequences_iff _ _ _).mp generated
        apply (mem_sequences_iff _ _ _).mpr
        constructor
        · simp only [observations, List.length_append] at bounded ⊢
          omega
        · intro atom inside
          exact supported atom (by
            rw [observations, ← List.append_assoc]
            exact List.mem_append_left _ inside)
      rw [Residual.run, actual_cut_uses_the_preserved_local_memory]
      have previous := ih old_generated
      rw [previous, observations]
      cases observed : receipt base capacity (schedule n) input
          (Residual.run (lift base capacity) schedule input seed n) site with
      | none => simp only [Option.toList_none, List.append_nil]
      | some atom =>
          simp only [remember, decode_encode base capacity _ old_generated,
            Option.toList_some, List.append_assoc]

theorem every_adaptive_cut_keeps_full_local_recall_across_planner_replacement
    (schedule : Residual.Schedule (lift base capacity))
    (supported : ∀ n strategy, schedule n = some strategy → strategy ∈ (lift base capacity).policies)
    (input : Input (lift base capacity)) (seed : State (lift base capacity)) (site : Fin base.sites)
    (prior : List (Notice base)) (initial : seed.frame.inbox site = encode base capacity prior)
    (prior_generated : prior ∈ memories base capacity) (n : Nat) (bounded : prior.length + n ≤ capacity) :
    decode base capacity ((Residual.run (lift base capacity) schedule input seed n).frame.inbox site) =
      some (prior ++ observations base capacity schedule input seed site n) := by
  have generated : prior ++ observations base capacity schedule input seed site n ∈ memories base capacity := by
    obtain ⟨_, old_supported⟩ := (mem_sequences_iff _ _ _).mp prior_generated
    apply (mem_sequences_iff _ _ _).mpr
    constructor
    · have small := observations_length base capacity schedule input seed site n
      simp only [List.length_append]
      omega
    · intro atom member
      rcases List.mem_append.mp member with old | fresh
      · exact old_supported atom old
      · exact observations_supported base capacity schedule supported input seed site n atom fresh
  rw [faithful_prefix base capacity schedule input seed site prior initial n generated]
  exact decode_encode base capacity _ generated

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Feedback
