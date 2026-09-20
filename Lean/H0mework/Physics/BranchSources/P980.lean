import H0mework.Arithmetic.ShellSources.P979

/-!
# Proposition 980: terminal confinement forces zero residual

This file separates the physical confinement argument from the arithmetic
readout.  The core theorem is about an arbitrary energy on an orbit:

```text
nonempty orbit
+ quantized terminal minimum
+ every nonzero terminal point carries permanent color holonomy
+ confinement forbids permanent color holonomy
=> the orbit contains a zero-residual point
```

The SU(7) specialization below uses only terminal physical branch cells, gauge orbit
membership, holonomy, singlet/non-singlet data, and a Lyapunov residual.  It
does not project through endpoint-code data.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Abstract terminal confinement -/

/-- A terminal energy point of an orbit is an in-orbit point whose energy is
minimal among all points of that orbit. -/
def TerminalEnergyPoint {X : Type*} (orbit : Set X) (E : X -> ℕ) (x : X) :
    Prop :=
  x ∈ orbit ∧ ∀ y : X, y ∈ orbit -> E x ≤ E y

/-- A quantized minimum certificate returns a terminal energy point whenever
the orbit is inhabited.  The quantization content is the well-founded `ℕ`
energy readout; no arithmetic endpoint semantics are assumed. -/
def QuantizedMinimum {X : Type*} (orbit : Set X) (E : X -> ℕ) : Prop :=
  orbit.Nonempty -> ∃ x : X, TerminalEnergyPoint orbit E x

/-- Terminal confinement principle.

If a nonempty quantized orbit has a terminal minimum, every nonzero terminal
minimum would be a permanent color holonomy, and confinement forbids all
permanent color holonomy, then the orbit contains a zero-residual point. -/
theorem terminalConfinement_zeroResidual
    {X : Type*} {orbit : Set X} {E : X -> ℕ}
    {PermanentColorHolonomy : X -> Prop}
    (hnonempty : orbit.Nonempty)
    (hminimum : QuantizedMinimum orbit E)
    (hterminal :
      ∀ x : X,
        TerminalEnergyPoint orbit E x ->
          E x ≠ 0 ->
            PermanentColorHolonomy x)
    (hconfinement : ∀ x : X, ¬ PermanentColorHolonomy x) :
    ∃ x : X, x ∈ orbit ∧ E x = 0 := by
  rcases hminimum hnonempty with ⟨x, hxterminal⟩
  by_cases hzero : E x = 0
  · exact ⟨x, hxterminal.1, hzero⟩
  · exact False.elim ((hconfinement x) (hterminal x hxterminal hzero))

/-! ## SU(7) physical orbit specialization -/

/-- A terminal physical SU(7) branch cell for one fiber.

The cell stores only representation/gauge data and a residual readout.  It is
deliberately not an endpoint-code object: the arithmetic projection is a later
readout layer, not part of the confinement producer. -/
structure SU7TerminalPhysicalBranchCell (n : ℕ) where
  leftWeight : Fin 7 -> ℤ
  rightWeight : Fin 7 -> ℤ
  colorLoop : Fin 3 -> ℤ
  gaugeAllowed : Prop
  colorSinglet : Prop
  nonSingletExcluded : Prop
  residual : ℕ
  permanentHolonomy : Prop

/-- Physical residual readout of a branch cell. -/
def terminalPhysicalResidual {n : ℕ}
    (cell : SU7TerminalPhysicalBranchCell n) : ℕ :=
  cell.residual

/-- Permanent color holonomy readout of a physical branch cell. -/
def terminalPhysicalPermanentColorHolonomy {n : ℕ}
    (cell : SU7TerminalPhysicalBranchCell n) : Prop :=
  cell.permanentHolonomy

/-- A terminal-confinement certificate for the SU(7) color orbit over one
fiber.  It packages only orbit nonemptiness, existence of a quantized terminal
minimum, the terminal nonzero-to-holonomy law, and confinement exclusion. -/
structure SU7ColorOrbitTerminalConfinement (n : ℕ) where
  orbit : Set (SU7TerminalPhysicalBranchCell n)
  orbit_nonempty : orbit.Nonempty
  quantized_minimum : QuantizedMinimum orbit terminalPhysicalResidual
  terminal_nonzero_to_holonomy :
    ∀ cell : SU7TerminalPhysicalBranchCell n,
      TerminalEnergyPoint orbit terminalPhysicalResidual cell ->
        terminalPhysicalResidual cell ≠ 0 ->
          terminalPhysicalPermanentColorHolonomy cell
  confinement_excludes_holonomy :
    ∀ cell : SU7TerminalPhysicalBranchCell n,
      ¬ terminalPhysicalPermanentColorHolonomy cell

/-- SU(7) terminal confinement produces a zero-residual physical branch cell
inside the orbit. -/
theorem su7ColorOrbitTerminalConfinement_zeroResidual_mem
    {n : ℕ} (C : SU7ColorOrbitTerminalConfinement n) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      cell ∈ C.orbit ∧ terminalPhysicalResidual cell = 0 :=
  terminalConfinement_zeroResidual
    C.orbit_nonempty
    C.quantized_minimum
    C.terminal_nonzero_to_holonomy
    C.confinement_excludes_holonomy

/-- SU(7) terminal confinement produces a zero-residual physical branch cell. -/
theorem su7ColorOrbitTerminalConfinement_zeroResidual
    {n : ℕ} (C : SU7ColorOrbitTerminalConfinement n) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 := by
  rcases su7ColorOrbitTerminalConfinement_zeroResidual_mem C with
    ⟨cell, _hmem, hzero⟩
  exact ⟨cell, hzero⟩

/-! ## Certificate -/

/-- P980 certificate: terminal confinement itself forces a zero-residual
physical branch cell before any endpoint-code projection is applied. -/
structure TerminalConfinementZeroResidualCertificate where
  abstract_zero_residual :
    ∀ {X : Type*} {orbit : Set X} {E : X -> ℕ}
      {PermanentColorHolonomy : X -> Prop},
      orbit.Nonempty ->
        QuantizedMinimum orbit E ->
          (∀ x : X,
            TerminalEnergyPoint orbit E x ->
              E x ≠ 0 ->
                PermanentColorHolonomy x) ->
            (∀ x : X, ¬ PermanentColorHolonomy x) ->
              ∃ x : X, x ∈ orbit ∧ E x = 0
  su7_zero_residual_mem :
    ∀ {n : ℕ} (C : SU7ColorOrbitTerminalConfinement n),
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        cell ∈ C.orbit ∧ terminalPhysicalResidual cell = 0
  su7_zero_residual :
    ∀ {n : ℕ}, SU7ColorOrbitTerminalConfinement n ->
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0

/-- Canonical P980 terminal-confinement certificate. -/
def terminalConfinementZeroResidualCertificate :
    TerminalConfinementZeroResidualCertificate where
  abstract_zero_residual := by
    intro X orbit E PermanentColorHolonomy hnonempty hminimum hterminal
      hconfinement
    exact
      terminalConfinement_zeroResidual
        hnonempty hminimum hterminal hconfinement
  su7_zero_residual_mem :=
    su7ColorOrbitTerminalConfinement_zeroResidual_mem
  su7_zero_residual :=
    su7ColorOrbitTerminalConfinement_zeroResidual


end
end StandardModelConstraint
end SaturationMonoid
