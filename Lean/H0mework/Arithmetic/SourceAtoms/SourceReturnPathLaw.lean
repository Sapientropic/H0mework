import H0mework.Arithmetic.SourceAtoms.SourceReturnPathGapDescent

/-!
# Source return-path law

This file extracts the remaining hard socket from
`SourceReturnPathGapDescent.lean` into a defect-independent source law.

The point is deliberately narrow:

```text
upper source repair demand at k+1
+ lower arithmetic atom-pair realization at k
-> source lower evidence returns to the upper evidence
```

It does not construct an atom pair at shell `k+1`, and it does not assume
arithmetic successor realization.  It is the next source/representation
obligation needed to make stable arithmetic projection defect impossible.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Bounded source return-path law.

This is stronger and cleaner than the socket in
`BoundedSourceReturnPathGapDescent`: it does not mention an upper defect.
The lower atom-pair realization is used only to force a source return path
from the lowered evidence back to the upper repair evidence. -/
structure BoundedSourceReturnPathLaw
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  path_antisymmetry :
    SourcePathAntisymmetry SourceEvidence Source
  lower_realization_returns :
    ∀ {k : Nat},
      k < target ->
        (upper : RepRepairDemand SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            Source.path
              (source_descent.lowerEvidence upper)
              upper.evidence

namespace BoundedSourceReturnPathLaw

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- A defect-independent source return-path law fills the hard socket of
`BoundedSourceReturnPathGapDescent`. -/
def toSourceReturnPathGapDescent
    (L :
      BoundedSourceReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    BoundedSourceReturnPathGapDescent
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := L.source_descent
  step_path := L.step_path
  path_antisymmetry := L.path_antisymmetry
  lower_realization_returns := by
    intro k hk defect hLowerRealization
    exact
      L.lower_realization_returns
        hk defect.demand hLowerRealization

/-- The source return-path law excludes target-shell arithmetic projection
defects once terminal no-third-sink is supplied. -/
theorem no_target_arithmetic_projection_defect
    (L :
      BoundedSourceReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_target_arithmetic_projection_defect

/-- A target defect extracts a first-class bounded persistent defect trace
from the defect-independent source return-path law once terminal no-third-sink
is supplied. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedSourceReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible under the
defect-independent source return-path law once terminal no-third-sink is
supplied. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (L :
      BoundedSourceReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_bounded_persistent_arithmetic_projection_defect_trace
      trace

/-- The defect-independent source return-path law excludes a target defect
through the explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedSourceReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level readout from the source return-path law.

This remains double-negated: the law rules out stable defect, but does not
extract endpoint atoms by computation or table search. -/
theorem not_not_atom_realization_of_target_demand
    (L :
      BoundedSourceReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.not_not_atom_realization_of_target_demand demand

/-- Boundary calibration for the defect-independent return law.

Because the law includes source path antisymmetry, any lower realization below
an upper repair demand would force a two-way source path between the upper
evidence and its strict residual predecessor.  This contradicts the residual
step.  Therefore this law is a hard rejection target, not a positive producer
interface for ordinary monotone source categories. -/
theorem no_lower_atom_realization_below_upper_demand
    (L :
      BoundedSourceReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target)
    (upper : RepRepairDemand SourceEvidence Residual n (k + 1)) :
    ¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  intro realization
  have hForward :
      Source.path upper.evidence
        (L.source_descent.lowerEvidence upper) :=
    L.step_path.step_is_path
      (L.source_descent.step_to_lower upper)
  have hReturn :
      Source.path
        (L.source_descent.lowerEvidence upper)
        upper.evidence :=
    L.lower_realization_returns hk upper realization
  have hEq :
      L.source_descent.lowerEvidence upper = upper.evidence :=
    L.path_antisymmetry.closes hForward hReturn
  have hStep :
      Residual.residualEnergy
          (L.source_descent.lowerEvidence upper) + 1 =
        Residual.residualEnergy upper.evidence :=
    Residual.step_decreases_one
      (L.source_descent.step_to_lower upper)
  have hImpossible :
      Residual.residualEnergy upper.evidence + 1 =
        Residual.residualEnergy upper.evidence := by
    rw [hEq] at hStep
    exact hStep
  have hlt :
      Residual.residualEnergy upper.evidence <
        Residual.residualEnergy upper.evidence := by
    calc
      Residual.residualEnergy upper.evidence <
          Residual.residualEnergy upper.evidence + 1 :=
        Nat.lt_succ_self _
      _ = Residual.residualEnergy upper.evidence := hImpossible
  exact (Nat.lt_irrefl _) hlt

end BoundedSourceReturnPathLaw

/-- Traced bounded source return-path law.

The return path itself is still source-side; trace data is carried by the
existing descent structure and is not used to manufacture endpoint atoms. -/
structure BoundedTracedSourceReturnPathLaw
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  path_antisymmetry :
    SourcePathAntisymmetry SourceEvidence Source
  lower_realization_returns :
    ∀ {k : Nat},
      k < target ->
        (upper :
          TracedFeasibleRepRepairDemand
            SourcePath PhaseTrace SigmaTag ProducerTrace
            SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            Source.path
              (source_descent.lowerEvidence upper.demand.demand)
              upper.demand.demand.evidence

namespace BoundedTracedSourceReturnPathLaw

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- A traced source return-path law fills the traced hard socket of
`BoundedTracedSourceReturnPathGapDescent`. -/
def toTracedSourceReturnPathGapDescent
    (L :
      BoundedTracedSourceReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    BoundedTracedSourceReturnPathGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := L.source_descent
  step_path := L.step_path
  trace_descent := L.trace_descent
  path_antisymmetry := L.path_antisymmetry
  lower_realization_returns := by
    intro k hk defect hLowerRealization
    exact
      L.lower_realization_returns
        hk defect.demand hLowerRealization

/-- The traced source return-path law excludes target-shell traced arithmetic
projection defects once traced terminal no-third-sink is supplied. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (L :
      BoundedTracedSourceReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  (L.toTracedSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace from the traced defect-independent source
return-path law once traced terminal no-third-sink is supplied. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedTracedSourceReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  (L.toTracedSourceReturnPathGapDescent terminal_no_third_sink)
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is impossible
under the traced defect-independent source return-path law once traced
terminal no-third-sink is supplied. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (L :
      BoundedTracedSourceReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  (L.toTracedSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- The traced defect-independent source return-path law excludes a target
traced feasible defect through the explicit bounded persistent trace midpoint.
-/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedTracedSourceReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  (L.toTracedSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level traced readout from the source return-path law. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (L :
      BoundedTracedSourceReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (L.toTracedSourceReturnPathGapDescent terminal_no_third_sink)
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

/-- Traced boundary calibration for the defect-independent return law.

As in the untraced version, a lower realization below an upper traced demand
would close a strict residual two-way source path. -/
theorem no_lower_atom_realization_below_upper_traced_demand
    (L :
      BoundedTracedSourceReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target)
    (upper :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n (k + 1)) :
    ¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  intro realization
  have hForward :
      Source.path upper.demand.demand.evidence
        (L.source_descent.lowerEvidence upper.demand.demand) :=
    L.step_path.step_is_path
      (L.source_descent.step_to_lower upper.demand.demand)
  have hReturn :
      Source.path
        (L.source_descent.lowerEvidence upper.demand.demand)
        upper.demand.demand.evidence :=
    L.lower_realization_returns hk upper realization
  have hEq :
      L.source_descent.lowerEvidence upper.demand.demand =
        upper.demand.demand.evidence :=
    L.path_antisymmetry.closes hForward hReturn
  have hStep :
      Residual.residualEnergy
          (L.source_descent.lowerEvidence upper.demand.demand) + 1 =
        Residual.residualEnergy upper.demand.demand.evidence :=
    Residual.step_decreases_one
      (L.source_descent.step_to_lower upper.demand.demand)
  have hImpossible :
      Residual.residualEnergy upper.demand.demand.evidence + 1 =
        Residual.residualEnergy upper.demand.demand.evidence := by
    rw [hEq] at hStep
    exact hStep
  have hlt :
      Residual.residualEnergy upper.demand.demand.evidence <
        Residual.residualEnergy upper.demand.demand.evidence := by
    calc
      Residual.residualEnergy upper.demand.demand.evidence <
          Residual.residualEnergy upper.demand.demand.evidence + 1 :=
        Nat.lt_succ_self _
      _ = Residual.residualEnergy upper.demand.demand.evidence :=
        hImpossible
  exact (Nat.lt_irrefl _) hlt

end BoundedTracedSourceReturnPathLaw


end RepresentationArithmeticAtomProjectionDefect
