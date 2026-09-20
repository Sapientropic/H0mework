import H0mework.Arithmetic.ProjectionDefect.SourceNoReturnGapDescent

/-!
# Defect-conditioned source-anchored no-return law

This file combines the source-anchor extraction shape with the graded
source no-return obstruction.

Compared with the earlier anchored return-path law, this version does not ask
for source path antisymmetry.  The contradiction is supplied by residual
grading:

```text
upper defect at k+1
+ lower atom-pair realization at k
-> source anchor
-> lower evidence -> anchor -> upper evidence
-> forbidden by residual-energy no-return
```

This keeps the hard gate source-native and avoids turning the route into an
endpoint-pair producer.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Defect-conditioned source anchor plus residual no-return.

The anchor is constructed only in the coexistence state of an upper defect and
a lower arithmetic realization.  It does not produce upper-shell endpoints. -/
structure BoundedDefectConditionedSourceAnchoredNoReturnLaw
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  path_residual_nonincreasing :
    SourceResidualPathNonincreasing SourceEvidence Residual Source
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

namespace BoundedDefectConditionedSourceAnchoredNoReturnLaw

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Anchored no-return data fills the source no-return gap-descent socket. -/
def toSourceNoReturnGapDescent
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    BoundedSourceNoReturnGapDescent
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := L.source_descent
  path_residual_nonincreasing := L.path_residual_nonincreasing
  lower_realization_returns := by
    intro k hk defect realization
    exact
      L.path_transitivity.trans
        (L.lower_to_anchor hk defect realization)
        (L.anchor_returns_to_upper hk defect realization)

/-- Anchored no-return data proves the minimal coexistence obstruction. -/
def toDefectRealizationCoexistenceObstruction
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    BoundedDefectRealizationCoexistenceObstruction
      Atomic SourceEvidence Residual n target :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.toDefectRealizationCoexistenceObstruction

/-- Anchored no-return gives one-step defect descent. -/
theorem descend_below
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.descend_below hk

/-- Anchored no-return sends a target defect down to a terminal defect. -/
theorem terminal_defect_of_target_defect
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.terminal_defect_of_target_defect

/-- Anchored no-return excludes target-shell arithmetic projection defects. -/
theorem no_target_arithmetic_projection_defect
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_target_arithmetic_projection_defect

/-- A bounded persistent defect trace is impossible under anchored
no-return. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace
from anchored no-return once terminal no-third-sink is supplied. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible under anchored
no-return once terminal no-third-sink is supplied. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_bounded_persistent_arithmetic_projection_defect_trace
      trace

/-- Anchored no-return excludes a target defect through the explicit bounded
persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level readout from anchored no-return.

The conclusion is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_demand
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (L.toSourceNoReturnGapDescent terminal_no_third_sink)
    |>.not_not_atom_realization_of_target_demand demand

end BoundedDefectConditionedSourceAnchoredNoReturnLaw

/-- Traced defect-conditioned source anchor plus residual no-return. -/
structure BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
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
  path_residual_nonincreasing :
    SourceResidualPathNonincreasing SourceEvidence Residual Source
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

namespace BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced anchored no-return data fills the traced source no-return
gap-descent socket. -/
def toTracedSourceNoReturnGapDescent
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    BoundedTracedSourceNoReturnGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := L.source_descent
  step_path := L.step_path
  trace_descent := L.trace_descent
  path_residual_nonincreasing := L.path_residual_nonincreasing
  lower_realization_returns := by
    intro k hk defect realization
    exact
      L.path_transitivity.trans
        (L.lower_to_anchor hk defect realization)
        (L.anchor_returns_to_upper hk defect realization)

/-- Traced anchored no-return data proves the traced coexistence obstruction.
-/
def toTracedDefectRealizationCoexistenceObstruction
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    BoundedTracedDefectRealizationCoexistenceObstruction
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.toTracedDefectRealizationCoexistenceObstruction

/-- Traced anchored no-return gives one-step traced defect descent. -/
theorem descend_below
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.descend_below hk

/-- Traced anchored no-return sends a target traced defect down to a terminal
traced defect. -/
theorem terminal_traced_feasible_defect_of_target_defect
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.terminal_traced_feasible_defect_of_target_defect

/-- Traced anchored no-return excludes target-shell traced projection
defects. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
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
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A bounded traced persistent defect trace is impossible under traced
anchored no-return. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace from traced anchored no-return once traced
terminal no-third-sink is supplied. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
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
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is impossible
under traced anchored no-return once traced terminal no-third-sink is supplied.
-/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
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
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- Traced anchored no-return excludes a target traced feasible defect through
the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
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
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level traced readout from anchored no-return.

The conclusion is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
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
  (L.toTracedSourceNoReturnGapDescent terminal_no_third_sink)
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

end BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw


end RepresentationArithmeticAtomProjectionDefect
