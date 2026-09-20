import H0mework.Arithmetic.ProjectionDefect.DefectConditionedSourceAnchoredNoReturnLaw

/-!
# Defect-conditioned source return forcing

This file isolates the remaining source-side extraction target:

```text
upper projection defect at k+1
+ lower atom-pair realization at k
-> source return from lowered evidence to upper evidence
```

It deliberately does not contain terminal discharge and does not contain the
residual no-return contradiction.  Those are downstream hard gates.  The
mathematical task left for GT/crystal/branching dynamics is to prove this
return-forcing socket from native source structure.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Coexistence-state source return forcing.

This is the narrow source/arithmetic interface: if an upper projection defect
coexists with a lower atom-pair realization, the source dynamics force a path
from the lowered source evidence back to the upper evidence. -/
structure BoundedDefectRealizationSourceReturnForcing
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  lower_realization_returns :
    ∀ {k : Nat},
      k < target ->
        (defect :
          AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            Source.path
              (source_descent.lowerEvidence defect.demand)
              defect.demand.evidence

namespace BoundedDefectRealizationSourceReturnForcing

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Return forcing plus residual no-return fills the source no-return
gap-descent socket. -/
def toSourceNoReturnGapDescent
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedSourceNoReturnGapDescent
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := F.source_descent
  path_residual_nonincreasing := path_residual_nonincreasing
  lower_realization_returns := F.lower_realization_returns

/-- Return forcing plus residual no-return proves the minimal coexistence
obstruction. -/
def toDefectRealizationCoexistenceObstruction
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedDefectRealizationCoexistenceObstruction
      Atomic SourceEvidence Residual n target :=
  (F.toSourceNoReturnGapDescent
    terminal_no_third_sink path_residual_nonincreasing)
    |>.toDefectRealizationCoexistenceObstruction

/-- Return forcing plus residual no-return excludes target defects. -/
theorem no_target_arithmetic_projection_defect
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (F.toSourceNoReturnGapDescent
    terminal_no_third_sink path_residual_nonincreasing)
    |>.no_target_arithmetic_projection_defect

/-- Return forcing plus residual no-return excludes bounded persistent defect
traces. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  (F.toSourceNoReturnGapDescent
    terminal_no_third_sink path_residual_nonincreasing)
    |>.no_persistent_arithmetic_projection_defect_trace trace

end BoundedDefectRealizationSourceReturnForcing

/-- Anchored return forcing without residual no-return.

This is the preferred native-source extraction target: construct an anchor in
the coexistence state, prove lower-to-anchor and anchor-to-upper paths, and
let transitivity compose the forbidden return. -/
structure BoundedDefectConditionedSourceAnchorReturnForcing
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
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

namespace BoundedDefectConditionedSourceAnchorReturnForcing

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Anchored return forcing composes to direct source return forcing. -/
def toSourceReturnForcing
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target) :
    BoundedDefectRealizationSourceReturnForcing
      Atomic SourceEvidence Residual Source n target where
  source_descent := A.source_descent
  lower_realization_returns := by
    intro k hk defect realization
    exact
      A.path_transitivity.trans
        (A.lower_to_anchor hk defect realization)
        (A.anchor_returns_to_upper hk defect realization)

/-- Anchored return forcing plus residual no-return fills the source
no-return gap-descent socket. -/
def toSourceNoReturnGapDescent
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedSourceNoReturnGapDescent
      Atomic SourceEvidence Residual Source n target :=
  A.toSourceReturnForcing.toSourceNoReturnGapDescent
    terminal_no_third_sink path_residual_nonincreasing

/-- Anchored return forcing plus residual no-return excludes target defects.
-/
theorem no_target_arithmetic_projection_defect
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  A.toSourceReturnForcing.no_target_arithmetic_projection_defect
    terminal_no_third_sink path_residual_nonincreasing

end BoundedDefectConditionedSourceAnchorReturnForcing

namespace BoundedDefectConditionedSourceAnchoredNoReturnLaw

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- The older combined anchored no-return law contains an anchored return
forcing socket.  This projection forgets the no-return field. -/
def toSourceAnchorReturnForcing
    (L :
      BoundedDefectConditionedSourceAnchoredNoReturnLaw
        Atomic SourceEvidence Residual Source n target) :
    BoundedDefectConditionedSourceAnchorReturnForcing
      Atomic SourceEvidence Residual Source n target where
  source_descent := L.source_descent
  path_transitivity := L.path_transitivity
  sourceAnchor := L.sourceAnchor
  lower_to_anchor := L.lower_to_anchor
  anchor_returns_to_upper := L.anchor_returns_to_upper

end BoundedDefectConditionedSourceAnchoredNoReturnLaw

/-- Traced coexistence-state source return forcing. -/
structure BoundedTracedDefectRealizationSourceReturnForcing
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
  lower_realization_returns :
    ∀ {k : Nat},
      k < target ->
        (defect :
          TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            Source.path
              (source_descent.lowerEvidence defect.demand.demand.demand)
              defect.demand.demand.demand.evidence

namespace BoundedTracedDefectRealizationSourceReturnForcing

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced return forcing plus residual no-return fills the traced source
no-return gap-descent socket. -/
def toTracedSourceNoReturnGapDescent
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedTracedSourceNoReturnGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := F.source_descent
  step_path := F.step_path
  trace_descent := F.trace_descent
  path_residual_nonincreasing := path_residual_nonincreasing
  lower_realization_returns := F.lower_realization_returns

/-- Traced return forcing plus residual no-return excludes traced target
defects. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  (F.toTracedSourceNoReturnGapDescent
    terminal_no_third_sink path_residual_nonincreasing)
    |>.no_target_traced_feasible_arithmetic_projection_defect

end BoundedTracedDefectRealizationSourceReturnForcing

/-- Traced anchored return forcing without residual no-return. -/
structure BoundedTracedDefectConditionedSourceAnchorReturnForcing
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

namespace BoundedTracedDefectConditionedSourceAnchorReturnForcing

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced anchored return forcing composes to direct traced return forcing.
-/
def toTracedSourceReturnForcing
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedDefectRealizationSourceReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  source_descent := A.source_descent
  step_path := A.step_path
  trace_descent := A.trace_descent
  lower_realization_returns := by
    intro k hk defect realization
    exact
      A.path_transitivity.trans
        (A.lower_to_anchor hk defect realization)
        (A.anchor_returns_to_upper hk defect realization)

/-- Traced anchored return forcing plus residual no-return excludes traced
target defects. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  A.toTracedSourceReturnForcing
    |>.no_target_traced_feasible_arithmetic_projection_defect
      terminal_no_third_sink path_residual_nonincreasing

end BoundedTracedDefectConditionedSourceAnchorReturnForcing

namespace BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- The older combined traced anchored no-return law contains a traced
anchored return-forcing socket. -/
def toTracedSourceAnchorReturnForcing
    (L :
      BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedDefectConditionedSourceAnchorReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  source_descent := L.source_descent
  step_path := L.step_path
  trace_descent := L.trace_descent
  path_transitivity := L.path_transitivity
  sourceAnchor := L.sourceAnchor
  lower_to_anchor := L.lower_to_anchor
  anchor_returns_to_upper := L.anchor_returns_to_upper

end BoundedTracedDefectConditionedSourceAnchoredNoReturnLaw


end RepresentationArithmeticAtomProjectionDefect
