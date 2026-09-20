import H0mework.Arithmetic.ProjectionDefect.GeneratedLoweringResidualNoReturn
import H0mework.Arithmetic.ProjectionDefect.BoundedPersistentProjectionDefectTrace
import H0mework.Arithmetic.SourceAtoms.UniformSourceReturnForcingInstability

/-!
# Trace-carried generated-lowering no-return stable domain

This file is the endpoint-cover-free generated-lowering no-return hard door.

It keeps only the fields used by the no-return proof:

```text
additive residual transport
generated source lowering dynamics
edge-level residual nonincrease
trace-preserving source descent
uniform lower-realization return forcing
terminal no-third-sink
```

No raw endpoint-code projection, endpoint-cover adapter, or atomhood readout is
stored here.  Those belong to separate source-cover routes.  This file proves
stable traced projection-defect exclusion from source dynamics alone plus the
terminal no-third-sink principle.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Minimal generated-lowering no-return stable projection domain.

The arithmetic realization appears only as a coexistence key for source
return forcing.  The domain does not contain endpoint-code support and does
not produce atom-pair successors. -/
structure TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat) where
  residual_transport :
    AdditiveResidualTransportCategory SourceEvidence
  lowering_dynamics :
    SourceUnitLoweringDynamics SourceEvidence
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence residual_transport
      lowering_dynamics.sourceCategory n
  edge_residual_nonincreasing :
    ∀ {source target : SourceEvidence},
      lowering_dynamics.edge source target ->
        residual_transport.residualEnergy target ≤
          residual_transport.residualEnergy source
  source_descent :
    SourceDemandOneStepDescent SourceEvidence residual_transport n
  step_path :
    ResidualStepSourcePathCompatibility
      SourceEvidence residual_transport lowering_dynamics.sourceCategory
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence residual_transport lowering_dynamics.sourceCategory n
  lower_realization_returns :
    ∀ {k : Nat},
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence residual_transport
          lowering_dynamics.sourceCategory n (k + 1)) ->
        (∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k) ->
          lowering_dynamics.sourceCategory.path
            (source_descent.lowerEvidence defect.demand.demand.demand)
            defect.demand.demand.demand.evidence

/-- Endpoint-cover-free trace-carried anchor form of the generated-lowering
no-return domain.

Instead of directly asking for the forbidden lower-to-upper return path, this
domain asks for a trace-carried anchor and two generated source paths:

```text
lowered evidence -> anchor(trace) -> upper defect evidence
```

Generated lowering path transitivity composes the two paths. -/
structure TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat) where
  residual_transport :
    AdditiveResidualTransportCategory SourceEvidence
  lowering_dynamics :
    SourceUnitLoweringDynamics SourceEvidence
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence residual_transport
      lowering_dynamics.sourceCategory n
  edge_residual_nonincreasing :
    ∀ {source target : SourceEvidence},
      lowering_dynamics.edge source target ->
        residual_transport.residualEnergy target ≤
          residual_transport.residualEnergy source
  source_descent :
    SourceDemandOneStepDescent SourceEvidence residual_transport n
  step_path :
    ResidualStepSourcePathCompatibility
      SourceEvidence residual_transport lowering_dynamics.sourceCategory
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence residual_transport lowering_dynamics.sourceCategory n
  anchorEvidence :
    SourceRepairTrace SourcePath PhaseTrace SigmaTag ProducerTrace ->
      SourceEvidence
  lowerToAnchor :
    ∀ {k : Nat},
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence residual_transport
          lowering_dynamics.sourceCategory n (k + 1)) ->
        (∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k) ->
          lowering_dynamics.sourceCategory.path
            (source_descent.lowerEvidence defect.demand.demand.demand)
            (anchorEvidence defect.demand.trace)
  anchorReturnsToUpper :
    ∀ {k : Nat},
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence residual_transport
          lowering_dynamics.sourceCategory n (k + 1)) ->
        (∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k) ->
          lowering_dynamics.sourceCategory.path
            (anchorEvidence defect.demand.trace)
            defect.demand.demand.demand.evidence

namespace TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n : Nat}

/-- The minimal domain exposes uniform traced source-return forcing. -/
def toUniformTracedDefectRealizationSourceReturnForcing
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    UniformTracedDefectRealizationSourceReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence D.residual_transport
      D.lowering_dynamics.sourceCategory n where
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  lower_realization_returns := D.lower_realization_returns

/-- Edge-level residual nonincrease extends to all generated source paths. -/
theorem sourceResidualPathNonincreasing
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    SourceResidualPathNonincreasing
      SourceEvidence D.residual_transport
      D.lowering_dynamics.sourceCategory :=
  D.lowering_dynamics.toSourceResidualPathNonincreasingOfEdges
    D.residual_transport D.edge_residual_nonincreasing

/-- The minimal generated-lowering no-return domain fills the traced
instability law. -/
def toTracedArithmeticProjectionDefectInstabilityLaw
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    TracedFeasibleArithmeticProjectionDefectInstabilityLaw
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence D.residual_transport
      D.lowering_dynamics.sourceCategory n :=
  D.toUniformTracedDefectRealizationSourceReturnForcing
    |>.toTracedArithmeticProjectionDefectInstabilityLaw
      D.terminal_no_third_sink
      D.sourceResidualPathNonincreasing

/-- Stable traced feasible projection defects cannot exist under the minimal
generated-lowering no-return domain. -/
theorem no_stable_traced_feasible_atom_projection_defect
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence D.residual_transport
          D.lowering_dynamics.sourceCategory n k) :=
  D.toTracedArithmeticProjectionDefectInstabilityLaw
    |>.no_stable_traced_feasible_arithmetic_projection_defect

/-- Target-shell traced feasible projection defects are impossible under the
minimal generated-lowering no-return domain. -/
theorem no_target_traced_feasible_atom_projection_defect
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    (target : Nat) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n target) :=
  D.no_stable_traced_feasible_atom_projection_defect target

/-- Persistent traced feasible projection-defect traces are impossible under
the minimal generated-lowering no-return domain. -/
theorem no_persistent_traced_feasible_atom_projection_defect_trace
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    {target : Nat}
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence D.residual_transport
            D.lowering_dynamics.sourceCategory n k)) :
    False :=
  (D.no_stable_traced_feasible_atom_projection_defect 0)
    (trace 0 (Nat.zero_le target))

/-- First-class bounded persistent traced feasible projection-defect traces
are impossible under the minimal generated-lowering no-return domain. -/
theorem no_bounded_persistent_traced_feasible_atom_projection_defect_trace
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    {target : Nat}
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n target) :
    False :=
  D.no_persistent_traced_feasible_atom_projection_defect_trace
    trace.defect_at

/-- Demand-level double-negated atom-pair readout from the minimal
generated-lowering no-return domain. -/
theorem not_not_atom_realization_of_traced_feasible_demand
    (D :
      TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    {k : Nat}
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  D.toTracedArithmeticProjectionDefectInstabilityLaw
    |>.not_not_atom_realization_of_traced_feasible_demand demand

end TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain

namespace TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n : Nat}

/-- Compose the trace-carried anchor paths into the minimal direct no-return
domain. -/
def toTraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    (D :
      TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    TraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence n where
  residual_transport := D.residual_transport
  lowering_dynamics := D.lowering_dynamics
  terminal_no_third_sink := D.terminal_no_third_sink
  edge_residual_nonincreasing := D.edge_residual_nonincreasing
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  lower_realization_returns := by
    intro k defect realization
    exact
      D.lowering_dynamics.sourcePathTransitivity.trans
        (D.lowerToAnchor defect realization)
        (D.anchorReturnsToUpper defect realization)

/-- The anchor form exposes uniform traced source-return forcing through the
minimal direct no-return domain. -/
def toUniformTracedDefectRealizationSourceReturnForcing
    (D :
      TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    UniformTracedDefectRealizationSourceReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence D.residual_transport
      D.lowering_dynamics.sourceCategory n :=
  D.toTraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    |>.toUniformTracedDefectRealizationSourceReturnForcing

/-- Stable traced feasible projection defects cannot exist under the
trace-carried anchor no-return domain. -/
theorem no_stable_traced_feasible_atom_projection_defect
    (D :
      TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence D.residual_transport
          D.lowering_dynamics.sourceCategory n k) :=
  D.toTraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    |>.no_stable_traced_feasible_atom_projection_defect

/-- Target-shell traced feasible projection defects are impossible under the
trace-carried anchor no-return domain. -/
theorem no_target_traced_feasible_atom_projection_defect
    (D :
      TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    (target : Nat) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n target) :=
  D.no_stable_traced_feasible_atom_projection_defect target

/-- Persistent traced feasible projection-defect traces are impossible under
the trace-carried anchor no-return domain. -/
theorem no_persistent_traced_feasible_atom_projection_defect_trace
    (D :
      TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    {target : Nat}
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence D.residual_transport
            D.lowering_dynamics.sourceCategory n k)) :
    False :=
  (D.no_stable_traced_feasible_atom_projection_defect 0)
    (trace 0 (Nat.zero_le target))

/-- First-class bounded persistent traced feasible projection-defect traces
are impossible under the trace-carried anchor no-return domain. -/
theorem no_bounded_persistent_traced_feasible_atom_projection_defect_trace
    (D :
      TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    {target : Nat}
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n target) :
    False :=
  D.no_persistent_traced_feasible_atom_projection_defect_trace
    trace.defect_at

/-- Demand-level double-negated atom-pair readout from the trace-carried
anchor no-return domain. -/
theorem not_not_atom_realization_of_traced_feasible_demand
    (D :
      TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    {k : Nat}
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  D.toTraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    |>.not_not_atom_realization_of_traced_feasible_demand demand

end TraceCarriedGeneratedLoweringAnchorNoReturnStableProjectionDomain


end RepresentationArithmeticAtomProjectionDefect
