import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceEnvelope
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryTrace
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

-- Both installations and callbacks may change at every actual cut.
def cursorAt : Nat → Cursor code
  | 0 => start
  | n + 1 => (cursorAt n).after (protocols n) (rivals n)
def stages : Nat → List (EventHistory.Stage (code := code))
  | 0 => []
  | n + 1 => stages n ++ [(protocols n, rivals n)]
abbrev state (n : Nat) := EventStep.seed (cursorAt start protocols rivals n)
abbrev row (n : Nat) := StageTrace.material (cursorAt start protocols rivals n) (protocols n) (rivals n)
abbrev baseline := OriginQueue.baseline start
abbrev rank (n : Nat) := (QueueScheduler.untried code (baseline start) (state start protocols rivals n).past).card
abbrev gap (n : Nat) := InterferenceEnvelope.gap start (StageTrace.records start (stages protocols rivals n))
abbrev warmup := start.ownerStart - (EventStep.seed start).history.length

omit [DecidableEq Port] [DecidableEq Technology] in
theorem stage_count (n : Nat) : (stages protocols rivals n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stages, List.length_append, List.length_singleton, ih]
theorem execute_stages (n : Nat) :
    EventHistory.execute start (stages protocols rivals n) = cursorAt start protocols rivals n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stages, StageQueue.execute_append, ih]; rfl
theorem records_succ (n : Nat) :
    StageTrace.records start (stages protocols rivals (n + 1)) =
      StageTrace.records start (stages protocols rivals n) ++ [row start protocols rivals n] := by
  rw [stages, StageQueue.records_append, execute_stages]; rfl
theorem row_at (n index : Nat) (bounded : index < n) :
    (StageTrace.records start (stages protocols rivals n))[index]? = some (row start protocols rivals index) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [records_succ, List.getElem?_append, StageTrace.record_count, stage_count]
    split
    · exact ih (by omega)
    · have same : index = n := by omega
      subst index; simp
theorem clocks (n : Nat) :
    (state start protocols rivals n).history.length = (EventStep.seed start).history.length + n ∧
    (state start protocols rivals n).remaining = (EventStep.seed start).remaining - n ∧
    (cursorAt start protocols rivals n).ownerStart = start.ownerStart := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    have next := EventStep.actual_next_state (cursorAt start protocols rivals n) (protocols n) (rivals n)
    refine ⟨?_, ?_, ih.2.2⟩
    · change (EventStep.seed ((cursorAt start protocols rivals n).after _ _)).history.length = _
      rw [next]
      change ((state start protocols rivals n).history ++ [_]).length = _
      simp only [List.length_append, List.length_singleton, ih.1]; omega
    · change (EventStep.seed ((cursorAt start protocols rivals n).after _ _)).remaining = _
      rw [next]
      change (state start protocols rivals n).remaining - 1 = _
      rw [ih.2.1]; omega
theorem extends_one (n : Nat) :
    (state start protocols rivals n).past <+: (state start protocols rivals (n + 1)).past ∧
    (state start protocols rivals n).frame.sent <+: (state start protocols rivals (n + 1)).frame.sent := by
  simpa only [state, cursorAt, EventStep.actual_next_state] using
    QueueScheduler.advance_preserves_memory_and_queue code (some (protocols n).work.val)
      (EventStep.applied (cursorAt start protocols rivals n) (protocols n) (rivals n)) (state start protocols rivals n)
theorem memory_queue (first last : Nat) (later : first ≤ last) :
    (state start protocols rivals first).past <+: (state start protocols rivals last).past ∧
    (state start protocols rivals first).frame.sent <+: (state start protocols rivals last).frame.sent := by
  induction last, later using Nat.le_induction with
  | base => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | succ last _ ih =>
    have next := extends_one start protocols rivals last
    exact ⟨ih.1.trans next.1, ih.2.trans next.2⟩
theorem later_untried (first last : Nat) (later : first ≤ last) :
    QueueScheduler.untried code (baseline start) (state start protocols rivals last).past ⊆
      QueueScheduler.untried code (baseline start) (state start protocols rivals first).past := by
  obtain ⟨more, same⟩ := (memory_queue start protocols rivals first last later).1
  rw [← same]
  exact QueueScheduler.untried_append_subset code _ _ _ (memory_queue start protocols rivals 0 first (Nat.zero_le _)).1.length_le
theorem external_in_each_pair (n : Nat) (started : warmup start ≤ n) :
    ∃ offset < 2, Distributed.Recall.Information.Agency.ownerAt code
      (cursorAt start protocols rivals (n + offset)).ownerStart (state start protocols rivals (n + offset)).history.length = none := by
  have reached : start.ownerStart ≤ (EventStep.seed start).history.length + n := by dsimp only [warmup] at started; omega
  by_cases positive : 0 < code.sites
  · by_cases even : ((EventStep.seed start).history.length + n - start.ownerStart) % 2 = 0
    · refine ⟨1, by omega, ?_⟩
      rw [(clocks start protocols rivals _).1, (clocks start protocols rivals _).2.2]
      simp only [Distributed.Recall.Information.Agency.ownerAt, dif_pos positive]
      rw [if_neg (by omega)]
    · refine ⟨0, by omega, ?_⟩
      rw [(clocks start protocols rivals _).1, (clocks start protocols rivals _).2.2]
      simp only [Nat.add_zero, Distributed.Recall.Information.Agency.ownerAt, dif_pos positive, if_neg even]
  · exact ⟨0, by omega, by simp only [Distributed.Recall.Information.Agency.ownerAt, dif_neg positive]⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryTrace
