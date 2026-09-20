import H0mework.Physics.ColorLoops.P996

/-!
# Proposition 997: zero color-holonomy observable gives zero trace physical loop

This is still a pure projection layer.  It does not mention endpoint codes,
prime edges, raw-code shells, or arithmetic.  It only projects the P993/P996
generated color-loop zero residual to a physical color-loop trace readout.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-- Physical color-loop trace: the sum of the three color-loop coordinates. -/
def physicalColorLoopTrace {n : ℕ}
    (cell : SU7TerminalPhysicalBranchCell n) : ℤ :=
  cell.colorLoop (0 : Fin 3) +
    cell.colorLoop (1 : Fin 3) +
      cell.colorLoop (2 : Fin 3)

/-- Exact physical color loop: all three color-loop coordinates vanish. -/
def PhysicalColorLoopExact {n : ℕ}
    (cell : SU7TerminalPhysicalBranchCell n) : Prop :=
  ∀ i : Fin 3, cell.colorLoop i = 0

/-- Physical zero-trace loop observable obtained before any endpoint or
arithmetic projection. -/
def ZeroTracePhysicalLoopObservable (n : ℕ) : Prop :=
  ∃ cell : SU7TerminalPhysicalBranchCell n,
    terminalPhysicalResidual cell = 0 ∧
      ¬ terminalPhysicalPermanentColorHolonomy cell ∧
        PhysicalColorLoopExact cell ∧
          physicalColorLoopTrace cell = 0

/-- A generated zero residual forces every generated color-loop coordinate to
vanish. -/
theorem generatedColorLoop_exact_of_residual_zero
    {n : ℕ} {cell : SU7GeneratedTerminalColorCell n}
    (hzero : generatedTerminalColorResidual cell = 0) :
    GeneratedTerminalColorLoopExact cell := by
  unfold generatedTerminalColorResidual at hzero
  rcases Nat.add_eq_zero_iff.mp hzero with ⟨h01, h2⟩
  rcases Nat.add_eq_zero_iff.mp h01 with ⟨h0, h1⟩
  intro i
  fin_cases i
  · exact Int.natAbs_eq_zero.mp h0
  · exact Int.natAbs_eq_zero.mp h1
  · exact Int.natAbs_eq_zero.mp h2

/-- Generated exactness projects to physical color-loop exactness. -/
theorem physicalColorLoopExact_of_generated_exact
    {n : ℕ} {cell : SU7GeneratedTerminalColorCell n}
    (hexact : GeneratedTerminalColorLoopExact cell) :
    PhysicalColorLoopExact (terminalPhysicalCellOfGeneratedColorCell cell) := by
  intro i
  exact hexact i

/-- Exact physical color loops have zero physical trace. -/
theorem physicalColorLoopTrace_eq_zero_of_exact
    {n : ℕ} {cell : SU7TerminalPhysicalBranchCell n}
    (hexact : PhysicalColorLoopExact cell) :
    physicalColorLoopTrace cell = 0 := by
  unfold physicalColorLoopTrace
  simp [hexact (0 : Fin 3), hexact (1 : Fin 3), hexact (2 : Fin 3)]

/-- A generated zero-residual cell projects to the zero-trace physical loop
observable. -/
theorem zeroTracePhysicalLoopObservable_of_generated_zero
    {n : ℕ} {cell : SU7GeneratedTerminalColorCell n}
    (hzero : generatedTerminalColorResidual cell = 0) :
    ZeroTracePhysicalLoopObservable n := by
  let pcell := terminalPhysicalCellOfGeneratedColorCell cell
  have hgenExact : GeneratedTerminalColorLoopExact cell :=
    generatedColorLoop_exact_of_residual_zero hzero
  have hphysExact : PhysicalColorLoopExact pcell :=
    physicalColorLoopExact_of_generated_exact hgenExact
  refine ⟨pcell, ?_, ?_, hphysExact, ?_⟩
  · simp [pcell, hzero]
  · intro hhol
    exact hhol hzero
  · exact physicalColorLoopTrace_eq_zero_of_exact hphysExact

/-- P997 main bridge: P993/P996 gives a zero-trace physical color loop. -/
theorem zeroTracePhysicalLoopObservable_of_fullOrbitIncidenceNormalizer
    (n : ℕ) :
    ZeroTracePhysicalLoopObservable n := by
  rcases zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer n with
    ⟨cell, _hmem, hzero⟩
  exact zeroTracePhysicalLoopObservable_of_generated_zero hzero

/-- The zero-trace physical loop observable includes the P996 zero holonomy
observable. -/
theorem zeroColorHolonomyObservable_of_zeroTracePhysicalLoopObservable
    {n : ℕ} (O : ZeroTracePhysicalLoopObservable n) :
    ZeroColorHolonomyObservable n := by
  rcases O with ⟨cell, hres, hno, _hexact, _htrace⟩
  exact ⟨cell, hres, hno⟩


end
end StandardModelConstraint
end SaturationMonoid
