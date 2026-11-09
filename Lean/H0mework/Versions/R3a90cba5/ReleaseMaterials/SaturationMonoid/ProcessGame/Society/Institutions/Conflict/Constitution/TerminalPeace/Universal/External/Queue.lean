import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Frontier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Queue

structure Position where
  source : Nat
  pending : Nat

variable (queue : Nat → Nat)

def next (position : Position) : Position :=
  match position.pending with
  | 0 => ⟨position.source + 1, queue (position.source + 1)⟩
  | remaining + 1 => ⟨position.source, remaining⟩

def runFrom (initial : Position) : Nat → Position
  | 0 => initial
  | n + 1 => next queue (runFrom initial n)

abbrev run := runFrom queue ⟨0, queue 0⟩

theorem runFrom_add (initial : Position) (n m : Nat) :
    runFrom queue initial (n + m) = runFrom queue (runFrom queue initial n) m := by
  induction m with
  | zero => rfl
  | succ m earlier =>
    change next queue (runFrom queue initial (n + m)) = next queue (runFrom queue (runFrom queue initial n) m)
    rw [earlier]

theorem the_original_visit_follows_its_entire_finite_queue (initial : Position) :
    runFrom queue initial (initial.pending + 1) =
      ⟨initial.source + 1, queue (initial.source + 1)⟩ := by
  generalize count : initial.pending = width
  induction width generalizing initial with
  | zero =>
    change next queue initial = _
    simp [next, count]
  | succ width earlier =>
    have remaining : (next queue initial).pending = width := by simp [next, count]
    have source : (next queue initial).source = initial.source := by simp [next, count]
    rw [show width + 1 + 1 = 1 + (width + 1) by omega, runFrom_add]
    change runFrom queue (next queue initial) (width + 1) = _
    rw [earlier (next queue initial) remaining, source]

universe u v
variable {Current : Type u} {Write : Type v} (currentAt : Nat → Current) (writeAt : Nat → Write)

/-- Arbitrarily many neutral external visits can be queued before
each due write. The queue is fixed at that write's original position. -/
def presentation : Trace Current Write where
  current visit := currentAt ((run queue visit).source)
  effect visit :=
    if (run queue visit).pending = 0 then some (writeAt ((run queue visit).source)) else none

theorem presentation_ordinal (visit : Nat) :
    (presentation queue currentAt writeAt).ordinal visit = (run queue visit).source := by
  induction visit with
  | zero => rfl
  | succ visit exactPrior =>
    change (presentation queue currentAt writeAt).ordinal visit +
      (presentation queue currentAt writeAt).width visit = (next queue (run queue visit)).source
    rw [exactPrior]
    cases remaining : (run queue visit).pending with
    | zero => simp [Trace.width, presentation, next, remaining]
    | succ n => simp [Trace.width, presentation, next, remaining]

theorem presentation_uses_only_the_original_writes :
    (presentation queue currentAt writeAt).Factors currentAt writeAt (presentation queue currentAt writeAt).ordinal := by
  apply (presentation queue currentAt writeAt).factor_of_checks currentAt writeAt rfl
  intro visit
  unfold Trace.Check
  cases remaining : (run queue visit).pending with
  | zero =>
    have effect : (presentation queue currentAt writeAt).effect visit = some (writeAt (run queue visit).source) := by
      simp [presentation, remaining]
    have current : (presentation queue currentAt writeAt).current (visit + 1) =
        currentAt ((run queue visit).source + 1) := by
      change currentAt (next queue (run queue visit)).source = _
      simp [next, remaining]
    rw [effect]
    exact ⟨congrArg writeAt (presentation_ordinal queue currentAt writeAt visit).symm,
      current.trans (by rw [presentation_ordinal])⟩
  | succ n =>
    have effect : (presentation queue currentAt writeAt).effect visit = none := by simp [presentation, remaining]
    rw [effect]
    change currentAt (next queue (run queue visit)).source = currentAt (run queue visit).source
    simp [next, remaining]

theorem every_finite_queue_schedule_progresses :
    (presentation queue currentAt writeAt).Progress := by
  intro cut
  have visits : ∃ visit, (run queue visit).source = cut := by
    induction cut with
    | zero => exact ⟨0, rfl⟩
    | succ cut earlier =>
      obtain ⟨visit, reached⟩ := earlier
      let prior := run queue visit
      refine ⟨visit + (prior.pending + 1), ?_⟩
      unfold run
      rw [runFrom_add, the_original_visit_follows_its_entire_finite_queue]
      exact congrArg (· + 1) reached
  obtain ⟨visit, reached⟩ := visits
  exact ⟨visit, (presentation_ordinal queue currentAt writeAt visit).trans reached |>.ge⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Queue
