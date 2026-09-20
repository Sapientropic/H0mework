import H0mework.Arithmetic.SourceAtoms.SourceAnchoredReturnPathLaw

/-!
# Defect-conditioned source-anchored return-path law

This file keeps the useful anchor decomposition while restoring the necessary
conditioning on an upper projection defect.

The defect-independent return law is too strong as a positive target: with
source path antisymmetry it forbids lower-shell realizations below any upper
repair demand.  The viable hard-gate shape is instead:

```text
upper projection defect at k+1
+ lower atom-pair realization at k
-> source anchor
-> lower evidence -> anchor -> upper evidence
-> forbidden source preloop
```

Thus lower realization is not globally forbidden; it is forbidden only to
coexist with a persistent upper defect.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Defect-conditioned source-anchored return-path law.

This is the positive extraction target after the boundary calibration of the
defect-independent law.  The source anchor is constructed in the coexistence
state of an upper defect and a lower realization; it is not an upper-shell
endpoint producer. -/
structure BoundedDefectConditionedSourceAnchoredReturnPathLaw
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
        (defect :
          AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourceEvidence
  lower_to_anchor :
    ∀ {k : Nat}
      (hk : k < target)
      (defect :
        AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (source_descent.lowerEvidence defect.demand)
          (sourceAnchor hk defect realization)
  anchor_returns_to_upper :
    ∀ {k : Nat}
      (hk : k < target)
      (defect :
        AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (sourceAnchor hk defect realization)
          defect.demand.evidence

namespace BoundedDefectConditionedSourceAnchoredReturnPathLaw

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Defect-conditioned anchored data fills the return-path gap-descent socket.
-/
def toSourceReturnPathGapDescent
    (L :
      BoundedDefectConditionedSourceAnchoredReturnPathLaw
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
    intro k hk defect realization
    exact
      L.path_transitivity.trans
        (L.lower_to_anchor hk defect realization)
        (L.anchor_returns_to_upper hk defect realization)

/-- Defect-conditioned source anchors exclude target-shell arithmetic
projection defects once terminal no-third-sink is supplied. -/
theorem no_target_arithmetic_projection_defect
    (L :
      BoundedDefectConditionedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_target_arithmetic_projection_defect

/-- A target defect extracts a first-class bounded persistent defect trace
from defect-conditioned source anchors once terminal no-third-sink is supplied.
-/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedDefectConditionedSourceAnchoredReturnPathLaw
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

/-- A first-class bounded persistent defect trace is impossible under
defect-conditioned source anchors once terminal no-third-sink is supplied. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (L :
      BoundedDefectConditionedSourceAnchoredReturnPathLaw
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

/-- Defect-conditioned source anchors exclude a target defect through the
explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedDefectConditionedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level readout from defect-conditioned source anchors. -/
theorem not_not_atom_realization_of_target_demand
    (L :
      BoundedDefectConditionedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (L.toSourceReturnPathGapDescent terminal_no_third_sink)
    |>.not_not_atom_realization_of_target_demand demand

end BoundedDefectConditionedSourceAnchoredReturnPathLaw

/-- Traced defect-conditioned source-anchored return-path law. -/
structure BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
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
        (defect :
          TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourceEvidence
  lower_to_anchor :
    ∀ {k : Nat}
      (hk : k < target)
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (source_descent.lowerEvidence defect.demand.demand.demand)
          (sourceAnchor hk defect realization)
  anchor_returns_to_upper :
    ∀ {k : Nat}
      (hk : k < target)
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (sourceAnchor hk defect realization)
          defect.demand.demand.demand.evidence

namespace BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced defect-conditioned anchored data fills the traced return-path
gap-descent socket. -/
def toTracedSourceReturnPathGapDescent
    (L :
      BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
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
    intro k hk defect realization
    exact
      L.path_transitivity.trans
        (L.lower_to_anchor hk defect realization)
        (L.anchor_returns_to_upper hk defect realization)

/-- Traced defect-conditioned source anchors exclude target-shell traced
arithmetic projection defects once traced terminal no-third-sink is supplied.
-/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (L :
      BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
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
traced feasible defect trace from traced defect-conditioned source anchors once
traced terminal no-third-sink is supplied. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
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
under traced defect-conditioned source anchors once traced terminal
no-third-sink is supplied. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (L :
      BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
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

/-- Traced defect-conditioned source anchors exclude a target traced feasible
defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
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

/-- Demand-level traced readout from defect-conditioned source anchors. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (L :
      BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
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

end BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw


end RepresentationArithmeticAtomProjectionDefect
