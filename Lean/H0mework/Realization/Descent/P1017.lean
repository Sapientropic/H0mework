import H0mework.Arithmetic.AtomicCodes.P1016

/-!
# Proposition 1017: closed terminal cycles split by descent

This file records the pure topology/descent producer requested by the current
thread, before any arithmetic or SU(7) endpoint projection.

The point is deliberately small:

* a directed consciousness cycle carries length, holonomy, H¹ obstruction, and
  a primitive predicate;
* the extra structure is not a stored two-primitive witness, but a descent law:
  an even closed cycle with no two-primitive cover admits a strict descent move;
* terminality means no descent move is available.

Therefore an even closed terminal cycle must have a two-primitive
decomposition.  This is the abstract producer shape needed before projecting to
color loops, endpoint balance, or arithmetic.
-/

namespace SaturationMonoid

noncomputable section

/-! ## Directed cycle skeleton -/

/-- Phase readout for the minimal directed-cycle skeleton.  It is integer-valued
here to keep the producer independent of analytic phase models. -/
abbrev Phase := Int

/-- H¹ obstruction readout for the minimal directed-cycle skeleton. -/
abbrev H1Class := Int

/-- A directed consciousness cycle: the compact carrier requested in the
thread.  The `primitive` field is a proposition attached to the cycle; the
descent space below decides how primitive cycles glue and descend. -/
structure DirectedConsciousnessCycle where
  length : ℕ
  holonomy : Phase
  obstruction : H1Class
  primitive : Prop

/-- The shorter theorem-facing name. -/
abbrev DirectedCycle := DirectedConsciousnessCycle

/-- Primitive cycles are read from the carrier, not from arithmetic primality. -/
def PrimitiveCycle (C : DirectedCycle) : Prop :=
  C.primitive

/-! ## Descent structure -/

/-- Extra topology/descent structure on the directed-cycle carrier.

The crucial field is `descent_of_no_twoPrimitive`: it says a closed even cycle
which cannot be covered by two primitive cycles is still reducible by one
descent step.  This is the non-circular producer law: the two-primitive witness
is not stored; its absence produces a lower-energy obstruction-reducing move.
-/
structure DirectedCycleDescentSpace where
  glue : DirectedCycle -> DirectedCycle -> DirectedCycle
  energy : DirectedCycle -> ℕ
  Descends : DirectedCycle -> DirectedCycle -> Prop
  descent_lowers_energy :
    ∀ {C D : DirectedCycle}, Descends C D -> energy D < energy C
  descent_of_no_twoPrimitive :
    ∀ C : DirectedCycle,
      Even C.length ->
        C.holonomy = 0 ->
          (¬ ∃ A B : DirectedCycle,
            PrimitiveCycle A ∧ PrimitiveCycle B ∧ glue A B = C) ->
            ∃ D : DirectedCycle, Descends C D

/-- Terminal under the supplied descent structure: no descent move remains. -/
def TerminalUnderDescent
    (S : DirectedCycleDescentSpace) (C : DirectedCycle) : Prop :=
  ∀ D : DirectedCycle, ¬ S.Descends C D

/-- A cycle has a two-primitive cover when it is a glue of two primitive
cycles. -/
def TwoPrimitiveDecomposition
    (S : DirectedCycleDescentSpace) (C : DirectedCycle) : Prop :=
  ∃ A B : DirectedCycle,
    PrimitiveCycle A ∧ PrimitiveCycle B ∧ S.glue A B = C

/-! ## Producer theorem -/

/-- If a closed even cycle has no two-primitive decomposition, then it is not
terminal: the descent structure supplies a genuine lower-energy move. -/
theorem not_terminal_of_no_twoPrimitiveDecomposition
    (S : DirectedCycleDescentSpace)
    (C : DirectedCycle)
    (hEven : Even C.length)
    (hClosed : C.holonomy = 0)
    (hNoSplit : ¬ TwoPrimitiveDecomposition S C) :
    ¬ TerminalUnderDescent S C := by
  intro hTerminal
  rcases S.descent_of_no_twoPrimitive C hEven hClosed hNoSplit with
    ⟨D, hdesc⟩
  exact (hTerminal D) hdesc

/-- The requested pure topological producer.

Closedness (`holonomy = 0`) plus terminality under an energy-lowering descent
space forces two-primitive coverage of an even directed cycle. -/
theorem evenCycle_twoPrimitiveDecomposition
    (S : DirectedCycleDescentSpace)
    (C : DirectedCycle)
    (hEven : Even C.length)
    (hClosed : C.holonomy = 0)
    (hTerminal : TerminalUnderDescent S C) :
    ∃ A B : DirectedCycle,
      PrimitiveCycle A ∧ PrimitiveCycle B ∧ S.glue A B = C := by
  classical
  by_contra hNoSplit
  exact
    (not_terminal_of_no_twoPrimitiveDecomposition
      S C hEven hClosed hNoSplit) hTerminal

/-- The same theorem packaged under the named decomposition predicate. -/
theorem terminal_even_closed_has_twoPrimitiveDecomposition
    (S : DirectedCycleDescentSpace)
    (C : DirectedCycle)
    (hEven : Even C.length)
    (hClosed : C.holonomy = 0)
    (hTerminal : TerminalUnderDescent S C) :
    TwoPrimitiveDecomposition S C :=
  evenCycle_twoPrimitiveDecomposition S C hEven hClosed hTerminal

/-! ## Certificate -/

/-- P1017 certificate: two-primitive coverage is produced by closedness plus
terminal descent, not assumed as a field of the terminal point. -/
structure DirectedCycleTwoPrimitiveProducerCertificate where
  no_split_gives_descent :
    ∀ (S : DirectedCycleDescentSpace) (C : DirectedCycle),
      Even C.length ->
        C.holonomy = 0 ->
          (¬ TwoPrimitiveDecomposition S C) ->
            ¬ TerminalUnderDescent S C
  terminal_closed_even_splits :
    ∀ (S : DirectedCycleDescentSpace) (C : DirectedCycle),
      Even C.length ->
        C.holonomy = 0 ->
          TerminalUnderDescent S C ->
            TwoPrimitiveDecomposition S C
  descent_steps_lower_energy :
    ∀ (S : DirectedCycleDescentSpace) {C D : DirectedCycle},
      S.Descends C D -> S.energy D < S.energy C

/-- Canonical P1017 certificate. -/
theorem directedCycleTwoPrimitiveProducerCertificate :
    DirectedCycleTwoPrimitiveProducerCertificate := by
  constructor
  · intro S C hEven hClosed hNoSplit
    exact not_terminal_of_no_twoPrimitiveDecomposition
      S C hEven hClosed hNoSplit
  · intro S C hEven hClosed hTerminal
    exact terminal_even_closed_has_twoPrimitiveDecomposition
      S C hEven hClosed hTerminal
  · intro S C D hdesc
    exact S.descent_lowers_energy hdesc


end
end SaturationMonoid
