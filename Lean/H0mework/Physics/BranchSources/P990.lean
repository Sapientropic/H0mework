import H0mework.Physics.BranchSources.P985

/-!
# Proposition 990: terminal-only confinement on the full SU(7) color orbit

P980 used a strong global no-holonomy hypothesis:

```text
∀ x, ¬ PermanentColorHolonomy x
```

That is too strong for the full generated SU(7) color orbit: charged sectors
can carry holonomy.  The physical claim needed for terminal confinement is
terminal-only:

```text
terminal x -> ¬ PermanentColorHolonomy x
```

This file proves the terminal-only theorem, then derives terminal no-holonomy
from a Lyapunov descent law: any holonomy point admits a lower-energy point in
the same orbit, so it cannot be terminal.  Finally, it applies that theorem to
the full SU(7) generated color orbit, without first filtering to the exact
sector.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open RunningSigmaBeta

set_option linter.defProp false

/-! ## Abstract terminal-only confinement -/

/-- Terminal-only confinement principle.

Only terminal points must be holonomy-free.  Non-terminal points in the same
orbit may carry holonomy. -/
theorem terminalConfinement_zeroResidual_terminalOnly
    {X : Type*} {orbit : Set X} {E : X -> ℕ}
    {PermanentColorHolonomy : X -> Prop}
    (hnonempty : orbit.Nonempty)
    (hminimum : QuantizedMinimum orbit E)
    (hterminal :
      ∀ x : X,
        TerminalEnergyPoint orbit E x ->
          E x ≠ 0 ->
            PermanentColorHolonomy x)
    (hterminal_no_holonomy :
      ∀ x : X,
        TerminalEnergyPoint orbit E x ->
          ¬ PermanentColorHolonomy x) :
    ∃ x : X, x ∈ orbit ∧ E x = 0 := by
  rcases hminimum hnonempty with ⟨x, hxterminal⟩
  by_cases hzero : E x = 0
  · exact ⟨x, hxterminal.1, hzero⟩
  · exact False.elim
      ((hterminal_no_holonomy x hxterminal)
        (hterminal x hxterminal hzero))

/-- A Lyapunov descent law for holonomy points implies terminal no-holonomy:
if holonomy always has a strictly lower in-orbit energy witness, it cannot be
minimal. -/
theorem terminal_no_holonomy_of_holonomy_descent
    {X : Type*} {orbit : Set X} {E : X -> ℕ}
    {PermanentColorHolonomy : X -> Prop}
    (hdescent :
      ∀ x : X,
        x ∈ orbit ->
          PermanentColorHolonomy x ->
            ∃ y : X, y ∈ orbit ∧ E y < E x) :
    ∀ x : X,
      TerminalEnergyPoint orbit E x ->
        ¬ PermanentColorHolonomy x := by
  intro x hxterminal hhol
  rcases hdescent x hxterminal.1 hhol with ⟨y, hymem, hylt⟩
  exact (Nat.not_lt_of_ge (hxterminal.2 y hymem)) hylt

/-- Terminal confinement from a holonomy-descent law. -/
theorem terminalConfinement_zeroResidual_of_holonomy_descent
    {X : Type*} {orbit : Set X} {E : X -> ℕ}
    {PermanentColorHolonomy : X -> Prop}
    (hnonempty : orbit.Nonempty)
    (hminimum : QuantizedMinimum orbit E)
    (hterminal :
      ∀ x : X,
        TerminalEnergyPoint orbit E x ->
          E x ≠ 0 ->
            PermanentColorHolonomy x)
    (hdescent :
      ∀ x : X,
        x ∈ orbit ->
          PermanentColorHolonomy x ->
            ∃ y : X, y ∈ orbit ∧ E y < E x) :
    ∃ x : X, x ∈ orbit ∧ E x = 0 :=
  terminalConfinement_zeroResidual_terminalOnly
    hnonempty hminimum hterminal
    (terminal_no_holonomy_of_holonomy_descent hdescent)

/-! ## Full SU(7) generated color orbit -/

/-- The full generated SU(7) terminal color orbit, before exact-sector
filtering. -/
def su7RepresentationFullTerminalColorOrbit (n : ℕ) :
    Set (SU7GeneratedTerminalColorCell n) :=
  {cell | cell ∈ su7RepresentationFullTerminalCells n}

/-- The color-neutral singlet ground cell belongs to the full generated
incidence spectrum. -/
def su7RepresentationFullGroundTerminalCell (n : ℕ) :
    SU7GeneratedTerminalColorCell n :=
  generatedTerminalColorCellOfRepresentationSlot n
    SU3FlagSchubertCell.e
    SU7BlockIncidence.positiveNegativeSinglet

/-- The full-orbit ground cell has zero generated color-loop residual. -/
theorem su7RepresentationFullGroundTerminalCell_residual_zero
    (n : ℕ) :
    generatedTerminalColorResidual
        (su7RepresentationFullGroundTerminalCell n) = 0 :=
  generatedRepresentationSingletTerminalCell_residual_zero
    n SU3FlagSchubertCell.e

/-- The color-neutral singlet ground cell belongs to the full generated
incidence spectrum. -/
theorem su7RepresentationFullGround_mem (n : ℕ) :
    su7RepresentationFullGroundTerminalCell n ∈
      su7RepresentationFullTerminalCells n := by
  unfold su7RepresentationFullGroundTerminalCell
    su7RepresentationFullTerminalCells
  exact List.mem_flatMap.mpr
    ⟨SU3FlagSchubertCell.e,
      by simp [SU3FlagSchubertCell.all],
      by
        exact List.mem_map.mpr
          ⟨SU7BlockIncidence.positiveNegativeSinglet,
            by simp [SU7BlockIncidence.all],
            rfl⟩⟩

/-- The full generated orbit is nonempty. -/
theorem su7RepresentationFullTerminalColorOrbit_nonempty
    (n : ℕ) :
    (su7RepresentationFullTerminalColorOrbit n).Nonempty :=
  ⟨su7RepresentationFullGroundTerminalCell n,
    su7RepresentationFullGround_mem n⟩

/-- The color-neutral singlet ground cell is terminal in the full generated
orbit because its computed residual is zero. -/
theorem su7RepresentationFullGround_terminal
    (n : ℕ) :
    TerminalEnergyPoint
      (su7RepresentationFullTerminalColorOrbit n)
      generatedTerminalColorResidual
      (su7RepresentationFullGroundTerminalCell n) := by
  constructor
  · exact su7RepresentationFullGround_mem n
  · intro cell _hmem
    rw [su7RepresentationFullGroundTerminalCell_residual_zero n]
    exact Nat.zero_le _

/-- The full generated orbit supplies a quantized minimum. -/
theorem quantizedMinimum_of_su7RepresentationFullTerminalColorOrbit
    (n : ℕ) :
    QuantizedMinimum
      (su7RepresentationFullTerminalColorOrbit n)
      generatedTerminalColorResidual := by
  intro _hnonempty
  exact
    ⟨su7RepresentationFullGroundTerminalCell n,
      su7RepresentationFullGround_terminal n⟩

/-- On the generated color-loop readout, nonzero residual is permanent
holonomy by definition. -/
theorem fullGeneratedColor_terminal_nonzero_to_holonomy
    {n : ℕ}
    (cell : SU7GeneratedTerminalColorCell n)
    (_hterminal :
      TerminalEnergyPoint
        (su7RepresentationFullTerminalColorOrbit n)
        generatedTerminalColorResidual cell)
    (hnonzero : generatedTerminalColorResidual cell ≠ 0) :
    generatedTerminalColorPermanentHolonomy cell := by
  exact hnonzero

/-- Full-orbit Lyapunov descent: every holonomy point can descend to the
color-neutral singlet ground cell of residual `0`. -/
theorem fullGeneratedColor_holonomy_descent
    {n : ℕ}
    (cell : SU7GeneratedTerminalColorCell n)
    (_hmem : cell ∈ su7RepresentationFullTerminalColorOrbit n)
    (hhol : generatedTerminalColorPermanentHolonomy cell) :
    ∃ y : SU7GeneratedTerminalColorCell n,
      y ∈ su7RepresentationFullTerminalColorOrbit n ∧
        generatedTerminalColorResidual y <
          generatedTerminalColorResidual cell := by
  refine
    ⟨su7RepresentationFullGroundTerminalCell n,
      su7RepresentationFullGround_mem n, ?_⟩
  have hpos : 0 < generatedTerminalColorResidual cell :=
    Nat.pos_of_ne_zero hhol
  simpa [su7RepresentationFullGroundTerminalCell_residual_zero n]
    using hpos

/-- Therefore terminal points of the full generated color orbit cannot carry
permanent holonomy. -/
theorem fullGeneratedColor_terminal_no_holonomy
    {n : ℕ}
    (cell : SU7GeneratedTerminalColorCell n)
    (hterminal :
      TerminalEnergyPoint
        (su7RepresentationFullTerminalColorOrbit n)
        generatedTerminalColorResidual cell) :
    ¬ generatedTerminalColorPermanentHolonomy cell :=
  terminal_no_holonomy_of_holonomy_descent
    (orbit := su7RepresentationFullTerminalColorOrbit n)
    (E := generatedTerminalColorResidual)
    (PermanentColorHolonomy := generatedTerminalColorPermanentHolonomy)
    (fun x hxmem hhol =>
      fullGeneratedColor_holonomy_descent x hxmem hhol)
    cell hterminal

/-- Full SU(7) generated terminal confinement produces a zero generated
color residual without pre-filtering to the exact sector. -/
theorem zeroGeneratedColorResidual_of_fullGeneratedTerminalConfinement
    (n : ℕ) :
    ∃ cell : SU7GeneratedTerminalColorCell n,
      cell ∈ su7RepresentationFullTerminalColorOrbit n ∧
        generatedTerminalColorResidual cell = 0 :=
  terminalConfinement_zeroResidual_of_holonomy_descent
    (su7RepresentationFullTerminalColorOrbit_nonempty n)
    (quantizedMinimum_of_su7RepresentationFullTerminalColorOrbit n)
    (fun cell hterminal hnonzero =>
      fullGeneratedColor_terminal_nonzero_to_holonomy
        cell hterminal hnonzero)
    (fun cell hmem hhol =>
      fullGeneratedColor_holonomy_descent cell hmem hhol)

/-- The full generated terminal-confinement zero residual projects to P980's
terminal physical branch-cell residual. -/
theorem zeroTerminalPhysicalResidual_of_fullGeneratedTerminalConfinement
    (n : ℕ) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 := by
  rcases zeroGeneratedColorResidual_of_fullGeneratedTerminalConfinement n with
    ⟨cell, _hmem, hzero⟩
  exact
    ⟨terminalPhysicalCellOfGeneratedColorCell cell,
      by simp [hzero]⟩

/-! ## Certificate -/

/-- P990 certificate: full-orbit terminal-only confinement replaces the
strong all-orbit no-holonomy requirement. -/
structure FullOrbitTerminalOnlyConfinementCertificate where
  abstract_terminal_only :
    ∀ {X : Type*} {orbit : Set X} {E : X -> ℕ}
      {PermanentColorHolonomy : X -> Prop},
      orbit.Nonempty ->
        QuantizedMinimum orbit E ->
          (∀ x : X,
            TerminalEnergyPoint orbit E x ->
              E x ≠ 0 ->
                PermanentColorHolonomy x) ->
            (∀ x : X,
              TerminalEnergyPoint orbit E x ->
                ¬ PermanentColorHolonomy x) ->
              ∃ x : X, x ∈ orbit ∧ E x = 0
  terminal_no_holonomy_from_descent :
    ∀ {X : Type*} {orbit : Set X} {E : X -> ℕ}
      {PermanentColorHolonomy : X -> Prop},
      (∀ x : X,
        x ∈ orbit ->
          PermanentColorHolonomy x ->
            ∃ y : X, y ∈ orbit ∧ E y < E x) ->
        ∀ x : X,
          TerminalEnergyPoint orbit E x ->
            ¬ PermanentColorHolonomy x
  full_orbit_zero_generated :
    ∀ n : ℕ,
      ∃ cell : SU7GeneratedTerminalColorCell n,
        cell ∈ su7RepresentationFullTerminalColorOrbit n ∧
          generatedTerminalColorResidual cell = 0
  full_orbit_zero_physical :
    ∀ n : ℕ,
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0

/-- Canonical P990 full-orbit terminal-only confinement certificate. -/
def fullOrbitTerminalOnlyConfinementCertificate :
    FullOrbitTerminalOnlyConfinementCertificate where
  abstract_terminal_only := by
    intro X orbit E PermanentColorHolonomy hnonempty hminimum hterminal
      hterminal_no_holonomy
    exact
      terminalConfinement_zeroResidual_terminalOnly
        hnonempty hminimum hterminal hterminal_no_holonomy
  terminal_no_holonomy_from_descent := by
    intro X orbit E PermanentColorHolonomy hdescent
    exact terminal_no_holonomy_of_holonomy_descent hdescent
  full_orbit_zero_generated :=
    zeroGeneratedColorResidual_of_fullGeneratedTerminalConfinement
  full_orbit_zero_physical :=
    zeroTerminalPhysicalResidual_of_fullGeneratedTerminalConfinement


end
end StandardModelConstraint
end SaturationMonoid
