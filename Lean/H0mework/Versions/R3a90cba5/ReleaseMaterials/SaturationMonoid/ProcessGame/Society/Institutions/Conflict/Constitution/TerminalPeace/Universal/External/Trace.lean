import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External

universe u v

/-- A presentation reads the full source current and, when it writes, the
actual effect. An empty effect is a visit with no source write. -/
structure Trace (Current : Type u) (Write : Type v) where
  current : Nat → Current
  effect : Nat → Option Write

namespace Trace

variable {Current : Type u} {Write : Type v} (trace : Trace Current Write)

def width (n : Nat) : Nat :=
  match trace.effect n with
  | none => 0
  | some _ => 1

def ordinal : Nat → Nat
  | 0 => 0
  | n + 1 => ordinal n + trace.width n

theorem ordinal_mono : Monotone trace.ordinal :=
  monotone_nat_of_le_succ fun n => Nat.le_add_right (trace.ordinal n) _

theorem ordinal_succ_le (n : Nat) : trace.ordinal (n + 1) ≤ trace.ordinal n + 1 := by
  have width : trace.width n ≤ 1 := by
    unfold Trace.width
    split <;> omega
  exact Nat.add_le_add_left width _

variable (currentAt : Nat → Current) (writeAt : Nat → Write)

def Check (n : Nat) : Prop :=
  match trace.effect n with
  | none => trace.current (n + 1) = trace.current n
  | some written =>
    written = writeAt (trace.ordinal n) ∧ trace.current (n + 1) = currentAt (trace.ordinal n + 1)

structure Factors (f : Nat → Nat) : Prop where
  initial : f 0 = 0
  next : ∀ n, f (n + 1) = f n + trace.width n
  reads : ∀ n, trace.current n = currentAt (f n)
  writes : ∀ n written, trace.effect n = some written → written = writeAt (f n)

private theorem forced_ordinal {f : Nat → Nat} (starts : f 0 = 0)
    (counts : ∀ n, f (n + 1) = f n + trace.width n) : f = trace.ordinal := by
  funext n
  induction n with
  | zero => exact starts
  | succ n earlier =>
    rw [counts, earlier]
    rfl

theorem read_at_checked_prefix (starts : trace.current 0 = currentAt 0)
    (n : Nat) (checks : ∀ j < n, trace.Check currentAt writeAt j) :
    trace.current n = currentAt (trace.ordinal n) := by
  induction n with
  | zero => exact starts
  | succ n earlier =>
    have step := checks n (Nat.lt_succ_self _)
    have prior := earlier (fun j small => checks j (Nat.lt_trans small (Nat.lt_succ_self _)))
    unfold Check at step
    cases emitted : trace.effect n with
    | none =>
      rw [emitted] at step
      rw [step, prior]
      simp [ordinal, width, emitted]
    | some written =>
      rw [emitted] at step
      rw [step.2]
      simp [ordinal, width, emitted]

theorem factor_of_checks (starts : trace.current 0 = currentAt 0)
    (checks : ∀ n, trace.Check currentAt writeAt n) :
    trace.Factors currentAt writeAt trace.ordinal := by
  refine ⟨rfl, fun _ => rfl, fun n => read_at_checked_prefix trace currentAt writeAt starts n
    (fun j _ => checks j), ?_⟩
  intro n written emitted
  have step := checks n
  unfold Check at step
  rw [emitted] at step
  exact step.1

theorem checks_of_factor {f : Nat → Nat} (factor : trace.Factors currentAt writeAt f) :
    trace.current 0 = currentAt 0 ∧ ∀ n, trace.Check currentAt writeAt n := by
  rw [forced_ordinal trace factor.initial factor.next] at factor
  refine ⟨factor.reads 0, fun n => ?_⟩
  unfold Check
  cases emitted : trace.effect n with
  | none =>
    have next := factor.reads (n + 1)
    rw [show trace.ordinal (n + 1) = trace.ordinal n by simp [ordinal, width, emitted]] at next
    exact next.trans (factor.reads n).symm
  | some written =>
    refine ⟨factor.writes n written emitted, ?_⟩
    simpa [ordinal, width, emitted] using factor.reads (n + 1)

theorem exact_local_checks_iff_unique_factor :
    (trace.current 0 = currentAt 0 ∧ ∀ n, trace.Check currentAt writeAt n) ↔
      ∃! f, trace.Factors currentAt writeAt f := by
  constructor
  · rintro ⟨starts, checks⟩
    exact ⟨trace.ordinal, factor_of_checks trace currentAt writeAt starts checks,
      fun _ factor => forced_ordinal trace factor.initial factor.next⟩
  · rintro ⟨_, factor, _⟩
    exact checks_of_factor trace currentAt writeAt factor

end Trace

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External
