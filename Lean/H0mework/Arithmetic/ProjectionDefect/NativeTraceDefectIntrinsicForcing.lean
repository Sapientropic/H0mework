import H0mework.Arithmetic.SourceAtoms.NativeTraceReturnHardDoorGeometry
import H0mework.Arithmetic.ProjectionDefect.DefectIntrinsicSourceReturnForcing

/-!
# Native trace defect-intrinsic forcing

This file keeps the hard-door engine frozen and records the missing extraction
step:

```text
real traced feasible defect
+ native trace-return sourcePath
-> source return read from defect.demand.trace.sourcePath
-> defect-intrinsic source-return forcing
```

No SU7 / FactorHolonomy owner target is imported here.  Endpoint projection
and selected-source readouts can instantiate this later; the return extraction
itself is source-side and defect-intrinsic.
-/

namespace RepresentationArithmeticAtomProjectionDefect

namespace NativeTraceHardDoor

universe u

namespace NativeTraceReturnSourcePath

variable {SourceEvidence : Type u}
variable {D : SourceUnitLoweringDynamics SourceEvidence}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {n : Nat}
variable {S : SourceDemandOneStepDescent SourceEvidence Residual n}

/-- A real native trace-return defect forces the source return from its own
trace payload.

This is the point that prevents the return certificate from being merely moved
around: the return is extracted from `defect.demand.trace.sourcePath`. -/
theorem defect_intrinsic_return
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    {k : Nat}
    (defect :
      TracedFeasibleAtomProjectionDefect
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n (k + 1)) :
    D.sourceCategory.path
      (S.lowerEvidence defect.demand.demand.demand)
      defect.demand.demand.demand.evidence :=
  (activeReturnPacket defect).lower_returns_to_upper

/-- Native trace-return payloads instantiate the existing defect-intrinsic
source-return forcing socket.

The only non-return field supplied from outside is the ordinary residual step
path compatibility.  The return field itself is `defect_intrinsic_return`. -/
def defectIntrinsicSourceReturnForcing
    (step_path :
      ResidualStepSourcePathCompatibility
        SourceEvidence Residual D.sourceCategory)
    (PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) :
    UniformTracedDefectIntrinsicSourceReturnForcing
      (NativeTraceReturnSourcePath D Residual n S)
      PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual D.sourceCategory n where
  source_descent := S
  step_path := step_path
  trace_descent :=
    traceDescent
      (D := D) (Residual := Residual) (n := n) (S := S)
      PhaseTrace SigmaTag ProducerTrace
  defect_returns := by
    intro _k defect
    exact defect_intrinsic_return defect

/-- Stable traced feasible defects are excluded through the existing
defect-intrinsic forcing hard-door once terminal discharge and path residual
nonincrease are supplied. -/
theorem no_stable_traced_feasible_defect_via_defect_intrinsic_forcing
    (step_path :
      ResidualStepSourcePathCompatibility
        SourceEvidence Residual D.sourceCategory)
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing
        SourceEvidence Residual D.sourceCategory) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          (NativeTraceReturnSourcePath D Residual n S)
          PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual D.sourceCategory n k) :=
  (defectIntrinsicSourceReturnForcing
      (D := D) (Residual := Residual) (n := n) (S := S)
      step_path PhaseTrace SigmaTag ProducerTrace Atomic)
    |>.no_stable_traced_feasible_arithmetic_projection_defect
      terminal_no_third_sink path_residual_nonincreasing

end NativeTraceReturnSourcePath

namespace NativeTraceReturnHardDoorGeometry

variable {PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n : Nat}

/-- A native trace-return hard-door geometry supplies defect-intrinsic source
return forcing through the trace payload itself.

This is the geometry-level form of the extraction theorem: the hard-door
geometry does not need an atom-pair successor realization to produce the
return field of `UniformTracedDefectIntrinsicSourceReturnForcing`. -/
def defectIntrinsicSourceReturnForcing
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n) :
    UniformTracedDefectIntrinsicSourceReturnForcing
      G.SourcePath
      PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence G.residual_transport
      G.lowering_dynamics.sourceCategory n :=
  NativeTraceReturnSourcePath.defectIntrinsicSourceReturnForcing
    (D := G.lowering_dynamics)
    (Residual := G.residual_transport)
    (n := n)
    (S := G.source_descent)
    G.step_path
    PhaseTrace SigmaTag ProducerTrace Atomic

/-- Stable traced feasible defects are impossible for a native trace-return
hard-door geometry through the defect-intrinsic forcing route.

This is parallel to the existing return-certificate theorem, but it records the
more important source-side fact: `defect_returns` is generated from the defect
trace payload. -/
theorem no_stable_traced_feasible_defect_via_defect_intrinsic_forcing
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          G.SourcePath
          PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence G.residual_transport
          G.lowering_dynamics.sourceCategory n k) :=
  G.defectIntrinsicSourceReturnForcing
    |>.no_stable_traced_feasible_arithmetic_projection_defect
      G.terminal_no_third_sink
      (G.lowering_dynamics.toSourceResidualPathNonincreasingOfEdges
        G.residual_transport
        (G.lowering_dynamics.edgeResidualNonincreasingOfPotentialReadout
          G.residual_transport G.residual_eq_potential))

end NativeTraceReturnHardDoorGeometry


end NativeTraceHardDoor

end RepresentationArithmeticAtomProjectionDefect
