import H0mework.Arithmetic.ProjectionDefect.TraceCarriedGeneratedLoweringNoReturnStableDomain
import H0mework.Arithmetic.ProjectionDefect.DefectIntrinsicSourceReturnForcing

/-!
# Trace-carried generated-lowering return certificate

This file extracts the source-trace obligation behind the generated-lowering
no-return hard door.

The existing minimal no-return domain asks for:

```text
upper defect at k+1
+ lower atom realization at k
-> generated source path from lowered evidence back to upper evidence
```

For native source traces, the stronger and cleaner target is often:

```text
upper defect trace itself carries lowered evidence -> upper evidence
```

This adapter records that source-side certificate directly, then forgets it to
the existing minimal no-return hard door.  It remains endpoint-free: no raw
code projection, endpoint cover, or atom-pair successor realization appears.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Endpoint-free generated-lowering no-return domain where the traced defect
itself carries the lower-to-upper source return certificate.

The `trace_returns_lower_to_upper` field does not depend on a lower atom-pair
realization.  This makes it a sharper source-side extraction target for
future SU7 / GT / crystal / branching trace laws. -/
structure TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
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
  trace_returns_lower_to_upper :
    ∀ {k : Nat},
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence residual_transport
          lowering_dynamics.sourceCategory n (k + 1)) ->
        lowering_dynamics.sourceCategory.path
          (source_descent.lowerEvidence defect.demand.demand.demand)
          defect.demand.demand.demand.evidence

namespace TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n : Nat}

/-- Forget the trace-carried return certificate to the minimal generated
lowering no-return hard door. -/
def toTraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    (D :
      TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
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
    intro _k defect _realization
    exact D.trace_returns_lower_to_upper defect

/-- Forget the generated-lowering no-return carrier to the generic intrinsic
source-return forcing socket.

This records the important boundary: the trace supplies a return from the
defect itself, so the older lower-realization input is unnecessary. -/
def toUniformTracedDefectIntrinsicSourceReturnForcing
    (D :
      TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n) :
    UniformTracedDefectIntrinsicSourceReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence D.residual_transport
      D.lowering_dynamics.sourceCategory n where
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  defect_returns := by
    intro _k defect
    exact D.trace_returns_lower_to_upper defect

/-- Trace-carried return certificates rule out stable traced feasible
projection defects under generated-lowering residual no-return. -/
theorem no_stable_traced_feasible_atom_projection_defect
    (D :
      TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
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

/-- Target-shell traced feasible projection defects are impossible from the
trace-carried return-certificate no-return adapter. -/
theorem no_target_traced_feasible_atom_projection_defect
    (D :
      TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    (target : Nat) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n target) :=
  D.no_stable_traced_feasible_atom_projection_defect target

/-- Persistent traced feasible projection-defect traces are impossible from
the trace-carried return-certificate no-return adapter. -/
theorem no_persistent_traced_feasible_atom_projection_defect_trace
    (D :
      TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
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
  D.toTraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    |>.no_persistent_traced_feasible_atom_projection_defect_trace
      trace

/-- First-class bounded persistent traced feasible projection-defect traces
are impossible from the trace-carried return-certificate no-return adapter. -/
theorem no_bounded_persistent_traced_feasible_atom_projection_defect_trace
    (D :
      TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence n)
    {target : Nat}
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence D.residual_transport
        D.lowering_dynamics.sourceCategory n target) :
    False :=
  D.toTraceCarriedGeneratedLoweringNoReturnStableProjectionDomain
    |>.no_bounded_persistent_traced_feasible_atom_projection_defect_trace
      trace

/-- Demand-level double-negated atom-pair readout from the trace-carried
return-certificate no-return adapter. -/
theorem not_not_atom_realization_of_traced_feasible_demand
    (D :
      TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
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

end TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain


end RepresentationArithmeticAtomProjectionDefect
