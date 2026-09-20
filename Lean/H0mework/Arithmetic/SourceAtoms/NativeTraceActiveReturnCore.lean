import H0mework.Arithmetic.ProjectionDefect.GeneratedLoweringResidualNoReturn

/-!
# Native trace active-return core

This file isolates the RAAPD hard door from the SU7 / FactorHolonomy owner
lines.

If a traced feasible defect carries a native source path that, for the active
upper demand, constructs

```text
lower upper -> anchor upper -> upper
```

then the successor-shell defect is impossible by generated-lowering no-return.
No endpoint coverage and no atom-pair successor realization are used.
-/

namespace RepresentationArithmeticAtomProjectionDefect

namespace NativeTraceHardDoor

universe u

/-- Generic native trace-return payload.

The payload is a constructor, not a stored one-off upper source: given the
active successor-shell demand, it constructs the anchor route from the source
descent lower evidence back to the active upper evidence. -/
structure NativeTraceReturnSourcePath
    {SourceEvidence : Type u}
    (D : SourceUnitLoweringDynamics SourceEvidence)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (S : SourceDemandOneStepDescent SourceEvidence Residual n) :
    Type u where
  anchor : SourceEvidence -> SourceEvidence
  lower_to_anchor :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n (k + 1)),
        D.sourceCategory.path
          (S.lowerEvidence demand)
          (anchor demand.evidence)
  anchor_returns_to_upper :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n (k + 1)),
        D.sourceCategory.path
          (anchor demand.evidence)
          demand.evidence

namespace NativeTraceReturnSourcePath

variable {SourceEvidence : Type u}
variable {D : SourceUnitLoweringDynamics SourceEvidence}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {n : Nat}
variable {S : SourceDemandOneStepDescent SourceEvidence Residual n}

/-- The native trace-return payload composes to a direct lower-to-upper
generated-lowering return for the active successor demand. -/
theorem lower_returns_to_upper
    (P : NativeTraceReturnSourcePath D Residual n S)
    {k : Nat}
    (demand : RepRepairDemand SourceEvidence Residual n (k + 1)) :
    D.sourceCategory.path
      (S.lowerEvidence demand)
      demand.evidence :=
  D.sourcePathTransitivity.trans
    (P.lower_to_anchor demand)
    (P.anchor_returns_to_upper demand)

/-- Trace descent preserves a native trace-return constructor payload. -/
def traceDescent
    (PhaseTrace SigmaTag ProducerTrace : Type u) :
    SourceRepairTraceDescent
      (NativeTraceReturnSourcePath D Residual n S)
      PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual D.sourceCategory n where
  lowerTrace := by
    intro _k demand
    exact demand.trace

/-- Active return packet read from a real traced feasible defect.

The packet is intentionally read from `defect.demand.trace.sourcePath`; it is
not supplied as a separate witness after the defect is formed. -/
structure ActiveReturnPacket
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    {k : Nat}
    (defect :
      TracedFeasibleAtomProjectionDefect
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n (k + 1)) :
    Prop where
  active_residual :
    Residual.residualEnergy defect.demand.demand.demand.evidence = k + 1
  lower_to_anchor :
    D.sourceCategory.path
      (S.lowerEvidence defect.demand.demand.demand)
      (defect.demand.trace.sourcePath.anchor
        defect.demand.demand.demand.evidence)
  anchor_returns_to_upper :
    D.sourceCategory.path
      (defect.demand.trace.sourcePath.anchor
        defect.demand.demand.demand.evidence)
      defect.demand.demand.demand.evidence
  lower_returns_to_upper :
    D.sourceCategory.path
      (S.lowerEvidence defect.demand.demand.demand)
      defect.demand.demand.demand.evidence

/-- A real traced feasible defect whose source path is a native return
constructor carries the active return packet. -/
theorem activeReturnPacket
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    {k : Nat}
    (defect :
      TracedFeasibleAtomProjectionDefect
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n (k + 1)) :
    ActiveReturnPacket defect where
  active_residual := defect.demand.demand.demand.residual_eq
  lower_to_anchor :=
    defect.demand.trace.sourcePath.lower_to_anchor
      defect.demand.demand.demand
  anchor_returns_to_upper :=
    defect.demand.trace.sourcePath.anchor_returns_to_upper
      defect.demand.demand.demand
  lower_returns_to_upper :=
    defect.demand.trace.sourcePath.lower_returns_to_upper
      defect.demand.demand.demand

/-- Successor-shell traced feasible defects are impossible once the trace
payload itself supplies the active lower-return packet.

This is the source-side hard gate: the contradiction is between the trace
payload's generated-lowering return and generated-lowering no-return after one
source descent. -/
theorem no_successor_traced_feasible_defect_by_active_return_packet
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source)
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    {k : Nat} :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n (k + 1)) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  have packet : ActiveReturnPacket defect :=
    activeReturnPacket defect
  have hNoReturn :
      ¬ D.sourceCategory.path
          (S.lowerEvidence defect.demand.demand.demand)
          defect.demand.demand.demand.evidence :=
    D.no_return_after_source_descent
      Residual residual_eq_potential S
      defect.demand.demand.demand
  exact hNoReturn packet.lower_returns_to_upper

/-- All-shell traced feasible defect exclusion from terminal no-third-sink plus
the active-return successor contradiction.

The terminal branch is supplied explicitly; the successor branch is generated
from the native trace-return payload. -/
theorem no_traced_feasible_defect_by_terminal_and_active_return_packet
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source)
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          (NativeTraceReturnSourcePath D Residual n S)
          PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual D.sourceCategory n k) := by
  intro k
  cases k with
  | zero =>
      exact
        no_terminal_traced_feasible_atom_projection_defect_of_no_third_sink
          terminal
  | succ k =>
      simpa [Nat.succ_eq_add_one] using
        (no_successor_traced_feasible_defect_by_active_return_packet
          (D := D) (Residual := Residual) (S := S)
          residual_eq_potential
          (PhaseTrace := PhaseTrace)
          (SigmaTag := SigmaTag)
          (ProducerTrace := ProducerTrace)
          (Atomic := Atomic)
          (k := k))

end NativeTraceReturnSourcePath


end NativeTraceHardDoor

end RepresentationArithmeticAtomProjectionDefect
