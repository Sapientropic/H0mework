import H0mework.Arithmetic.SourceAtoms.SourceReturnPathLaw

/-!
# Source-anchored return-path law

This file splits the source return-path law into a source anchor extraction
plus source-path composition.

The intended future GT/crystal/SU7 proof shape is:

```text
lower atom-pair realization
-> source anchor in the lower shell/sector
-> source path from the actual lowered evidence to that anchor
-> source return path from the anchor to the upper evidence
```

Composing the two source paths fills `SourceReturnPathLaw.lean`.  No endpoint
atom pair is constructed at the upper shell.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Source path transitivity, kept separate from
`RepresentationFeasibleCategory` so existing source categories do not gain
extra obligations retroactively. -/
structure SourcePathTransitivity
    (SourceEvidence : Type u)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  trans :
    ∀ {a b c : SourceEvidence},
      Source.path a b ->
        Source.path b c ->
          Source.path a c

/-- Bounded source-anchored return-path law.

The lower atom realization is not transported to an upper atom realization.
It only selects a source anchor and source paths.  The final upper return path
is obtained by path transitivity. -/
structure BoundedSourceAnchoredReturnPathLaw
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
  path_transitivity :
    SourcePathTransitivity SourceEvidence Source
  sourceAnchor :
    ∀ {k : Nat},
      k < target ->
        (upper : RepRepairDemand SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourceEvidence
  lower_to_anchor :
    ∀ {k : Nat}
      (hk : k < target)
      (upper : RepRepairDemand SourceEvidence Residual n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (source_descent.lowerEvidence upper)
          (sourceAnchor hk upper realization)
  anchor_returns_to_upper :
    ∀ {k : Nat}
      (hk : k < target)
      (upper : RepRepairDemand SourceEvidence Residual n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (sourceAnchor hk upper realization)
          upper.evidence

namespace BoundedSourceAnchoredReturnPathLaw

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Source-anchored return-path data composes to the lower-level source
return-path law. -/
def toSourceReturnPathLaw
    (L :
      BoundedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target) :
    BoundedSourceReturnPathLaw
      Atomic SourceEvidence Residual Source n target where
  source_descent := L.source_descent
  step_path := L.step_path
  path_antisymmetry := L.path_antisymmetry
  lower_realization_returns := by
    intro k hk upper realization
    exact
      L.path_transitivity.trans
        (L.lower_to_anchor hk upper realization)
        (L.anchor_returns_to_upper hk upper realization)

/-- Source-anchored return-path data excludes target-shell arithmetic
projection defects once terminal no-third-sink is supplied. -/
theorem no_target_arithmetic_projection_defect
    (L :
      BoundedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  L.toSourceReturnPathLaw.no_target_arithmetic_projection_defect
    terminal_no_third_sink

/-- A target defect extracts a first-class bounded persistent defect trace
from source-anchored return-path data once terminal no-third-sink is supplied.
-/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  L.toSourceReturnPathLaw
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      terminal_no_third_sink target_defect

/-- A first-class bounded persistent defect trace is impossible under
source-anchored return-path data once terminal no-third-sink is supplied. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (L :
      BoundedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  L.toSourceReturnPathLaw
    |>.no_bounded_persistent_arithmetic_projection_defect_trace
      terminal_no_third_sink trace

/-- Source-anchored return-path data excludes a target defect through the
explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  L.toSourceReturnPathLaw
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace
      terminal_no_third_sink

/-- Demand-level readout from source-anchored return-path data. -/
theorem not_not_atom_realization_of_target_demand
    (L :
      BoundedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  L.toSourceReturnPathLaw.not_not_atom_realization_of_target_demand
    terminal_no_third_sink demand

end BoundedSourceAnchoredReturnPathLaw

/-- Traced source-anchored return-path law.

Trace data stays attached to the upper repair demand; the anchor law itself is
still a source-path construction and does not certify upper endpoints. -/
structure BoundedTracedSourceAnchoredReturnPathLaw
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
  path_transitivity :
    SourcePathTransitivity SourceEvidence Source
  sourceAnchor :
    ∀ {k : Nat},
      k < target ->
        (upper :
          TracedFeasibleRepRepairDemand
            SourcePath PhaseTrace SigmaTag ProducerTrace
            SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourceEvidence
  lower_to_anchor :
    ∀ {k : Nat}
      (hk : k < target)
      (upper :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (source_descent.lowerEvidence upper.demand.demand)
          (sourceAnchor hk upper realization)
  anchor_returns_to_upper :
    ∀ {k : Nat}
      (hk : k < target)
      (upper :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (sourceAnchor hk upper realization)
          upper.demand.demand.evidence

namespace BoundedTracedSourceAnchoredReturnPathLaw

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced source-anchored return-path data composes to the traced source
return-path law. -/
def toTracedSourceReturnPathLaw
    (L :
      BoundedTracedSourceAnchoredReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedSourceReturnPathLaw
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  source_descent := L.source_descent
  step_path := L.step_path
  trace_descent := L.trace_descent
  path_antisymmetry := L.path_antisymmetry
  lower_realization_returns := by
    intro k hk upper realization
    exact
      L.path_transitivity.trans
        (L.lower_to_anchor hk upper realization)
        (L.anchor_returns_to_upper hk upper realization)

/-- Traced source-anchored return-path data excludes target-shell traced
arithmetic projection defects once traced terminal no-third-sink is supplied.
-/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (L :
      BoundedTracedSourceAnchoredReturnPathLaw
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
  L.toTracedSourceReturnPathLaw
    |>.no_target_traced_feasible_arithmetic_projection_defect
      terminal_no_third_sink

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace from traced source-anchored return-path data once
traced terminal no-third-sink is supplied. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedTracedSourceAnchoredReturnPathLaw
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
  L.toTracedSourceReturnPathLaw
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      terminal_no_third_sink target_defect

/-- A first-class bounded persistent traced feasible defect trace is impossible
under traced source-anchored return-path data once traced terminal no-third-sink
is supplied. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (L :
      BoundedTracedSourceAnchoredReturnPathLaw
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
  L.toTracedSourceReturnPathLaw
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      terminal_no_third_sink trace

/-- Traced source-anchored return-path data excludes a target traced feasible
defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedTracedSourceAnchoredReturnPathLaw
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
  L.toTracedSourceReturnPathLaw
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
      terminal_no_third_sink

/-- Demand-level traced readout from source-anchored return-path data. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (L :
      BoundedTracedSourceAnchoredReturnPathLaw
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
  L.toTracedSourceReturnPathLaw
    |>.not_not_atom_realization_of_target_traced_feasible_demand
      terminal_no_third_sink demand

end BoundedTracedSourceAnchoredReturnPathLaw


end RepresentationArithmeticAtomProjectionDefect
