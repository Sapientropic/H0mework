import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Network

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root Lean

/-- Appending future requests cannot rewrite an already consumed source current. -/
theorem window_append_keeps_consumed_current {plan : Plan} (window : Continuation.Window plan)
    (requests suffix : List Continuation.Request) (n : Nat) (paid : n ≤ requests.length+1) :
    window.current (requests++suffix) n = window.current requests n := by
  induction n with
  | zero => unfold Continuation.Window.current; rfl
  | succ n ih =>
    rw [window.current_succ,window.current_succ,ih (by omega)]
    congr 1
    split
    · rfl
    · unfold Continuation.Window.emit
      rw [window.current_round]
      simp only [Nat.add_sub_cancel_left]
      congr 1
      unfold Continuation.Window.requestAt
      rw [List.getElem?_append_left (by omega : n-1 < requests.length)]

theorem handoff_append_keeps_consumed_current {plan : Plan} (seed : Handoff.Seed plan)
    (requests suffix : List Handoff.Request) (n : Nat) (paid : n ≤ seed.ordinal+requests.length+1) :
    seed.current (requests++suffix) n = seed.current requests n := by
  induction n with
  | zero => unfold Handoff.Seed.current; rfl
  | succ n ih =>
    rw [seed.current_succ,seed.current_succ,ih (by omega)]
    congr 1
    split
    · rfl
    · unfold Handoff.Seed.emit
      rw [seed.current_round]
      simp only [Nat.add_sub_cancel_left]
      split
      · rfl
      · congr 1
        unfold Handoff.Seed.requestAt
        rw [List.getElem?_append_left (by omega : n-(seed.ordinal+1) < requests.length)]

/-- The committed parent's two actual nexts stay related; their private states need not be equal. -/
theorem online_handoff_preserves_parent_next_and_complete_reply {lp rp : Plan}
    {left : Handoff.Seed lp} {right : Handoff.Seed rp} (same : SeedTwin left right)
    (requests : List Handoff.Request) (request : Handoff.Request) (nextCut : Nat) :
    let n := left.ordinal+requests.length+1
    left.current (requests++[request]) n = left.current requests n ∧
    right.current (requests++[request]) n = right.current requests n ∧
    Twin (left.current (requests++[request]) (n+1)) (right.current (requests++[request]) (n+1)) ∧
    handoffJson left (requests++[request]) n nextCut = handoffJson right (requests++[request]) n nextCut := by
  dsimp only
  exact ⟨handoff_append_keeps_consumed_current left requests [request] _ (by omega),
    handoff_append_keeps_consumed_current right requests [request] _ (by rw [← same.ordinal]),
    same.current _ _,same.complete _ _ _⟩

theorem online_handoff_next_is_own_root {plan : Plan} (seed : Handoff.Seed plan)
    (requests : List Handoff.Request) (request : Handoff.Request) :
    seed.current (requests++[request]) (seed.ordinal+requests.length+2) =
      ProgrammeSource.rawCurrent (seed.input (requests++[request]))
        (ProgrammeHistory.visitAt (seed.input (requests++[request]))
          (seed.ordinal+requests.length+2)).current :=
  (seed.current_is_own_root_current _ _).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
