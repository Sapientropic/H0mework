import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Words

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure WindowTwin {lp rp : Plan} (left : Continuation.Window lp) (right : Continuation.Window rp) : Prop where
  scope : left.scope = right.scope
  candidate : lp.candidate = rp.candidate
  initial : Twin left.initial right.initial

theorem WindowTwin.current {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n : Nat) :
    Twin (left.current requests n) (right.current requests n) := by
  induction n with
  | zero => unfold Continuation.Window.current; exact same.initial
  | succ n ih =>
    rw [left.current_succ,right.current_succ]
    have lawEq : left.law = right.law := congrArg (Mandate.law energyBase) same.scope
    rw [← lawEq]
    by_cases bootstrap : n = 0
    · simp only [if_pos bootstrap]
      exact ih.next left.scope rfl [] (by simp)
    · simp only [if_neg bootstrap,left.emission_uses_exact_request,right.emission_uses_exact_request]
      have word := ih.window_word left right same.scope same.candidate (left.requestAt requests n)
      change left.word (left.requestAt requests n) _ = right.word (right.requestAt requests n) _ at word
      rw [← word]
      exact ih.next left.scope rfl _ (window_word_energy _ _ _)

theorem WindowTwin.openPaid {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n : Nat) :
    left.openPaid requests n ↔ right.openPaid requests n := by
  have twin := same.current requests n
  have paid : left.law.Valid (left.current requests n) applicationFee ↔
      right.law.Valid (right.current requests n) applicationFee := by
    change (law left.scope).Valid _ _ ↔ (law right.scope).Valid _ _
    rw [← same.scope]
    exact twin.valid _ _ (energy_public _ rfl _ _ ((stable_application).2 (left.current requests n)))
  simp only [Continuation.Window.openPaid,Continuation.Window.requestAt,Quiet,
    same.scope,twin.technology,twin.clock,paid]

theorem WindowTwin.nextWindow {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n : Nat) :
    Option.Rel WindowTwin (left.nextWindow requests n) (right.nextWindow requests n) := by
  unfold Continuation.Window.nextWindow
  simp only [same.openPaid requests n]
  split
  · apply Option.Rel.some
    refine ⟨?_,same.candidate,same.current requests (n+1)⟩
    have clock := (same.current requests (n+1)).clock
    change (⟨_,_,_,_,_⟩ : Scope) = ⟨_,_,_,_,_⟩
    simp only [clock]
  · exact Option.Rel.none

structure SeedTwin {lp rp : Plan} (left : Handoff.Seed lp) (right : Handoff.Seed rp) : Prop where
  window : WindowTwin left.window right.window
  requests : left.requests = right.requests
  ordinal : left.ordinal = right.ordinal

theorem SeedTwin.current {lp rp : Plan} {left : Handoff.Seed lp} {right : Handoff.Seed rp}
    (same : SeedTwin left right) (requests : List Handoff.Request) (n : Nat) :
    Twin (left.current requests n) (right.current requests n) := by
  induction n with
  | zero => unfold Handoff.Seed.current; exact same.window.initial
  | succ n ih =>
    rw [left.current_succ,right.current_succ]
    have scope : left.scope = right.scope := same.window.scope
    have lawEq : left.law = right.law := congrArg (Mandate.law energyBase) scope
    rw [← lawEq]
    by_cases bootstrap : n = 0
    · simp only [if_pos bootstrap]
      exact ih.next left.scope rfl [] (by simp)
    · simp only [if_neg bootstrap,Handoff.Seed.emit]
      simp only [ih.round,same.window.initial.round,same.ordinal]
      split
      · rw [same.requests]
        have words := ih.window_word left.window right.window same.window.scope same.window.candidate
          (right.window.requestAt right.requests ((right.current requests n).round-right.window.initial.round))
        change left.window.word _ _ = right.window.word _ _ at words
        simp only [Continuation.Window.emit]
        rw [ih.round,same.window.initial.round]
        rw [← words]
        exact ih.next left.scope rfl _ (window_word_energy _ _ _)
      · have request : left.requestAt requests ((right.current requests n).round-right.window.initial.round) =
            right.requestAt requests ((right.current requests n).round-right.window.initial.round) := by
          simp only [Handoff.Seed.requestAt,same.ordinal,same.window.candidate]
        rw [request]
        rw [← ih.handoff_word left right scope]
        exact ih.next left.scope rfl _ (handoff_word_energy _ _ _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
