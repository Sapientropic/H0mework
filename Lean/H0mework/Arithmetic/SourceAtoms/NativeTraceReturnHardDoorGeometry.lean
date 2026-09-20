import H0mework.Arithmetic.SourceAtoms.NativeTraceReturnCertificateAdapter

/-!
# Native trace return hard-door geometry

This file packages the verified SU7-free native trace-return hard door into a
small source-geometry socket.

It is deliberately endpoint-free.  A future concrete Borromean/SU7 instance
must supply source residual/lowering/terminal data; the trace path type is then
the native return constructor payload from `NativeTraceActiveReturnCore.lean`.
-/

namespace RepresentationArithmeticAtomProjectionDefect

namespace NativeTraceHardDoor

universe u

/-- Minimal source-side geometry for the native trace active-return hard door.

The fields are exactly the upstream obligations needed to feed the existing
RAAPD generated-lowering return-certificate domain. -/
structure NativeTraceReturnHardDoorGeometry
    (PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop)
    (SourceEvidence : Type u)
    (n : Nat) where
  residual_transport :
    AdditiveResidualTransportCategory SourceEvidence
  lowering_dynamics :
    SourceUnitLoweringDynamics SourceEvidence
  residual_eq_potential :
    ∀ source : SourceEvidence,
      residual_transport.residualEnergy source =
        lowering_dynamics.potential source
  source_descent :
    SourceDemandOneStepDescent
      SourceEvidence residual_transport n
  step_path :
    ResidualStepSourcePathCompatibility
      SourceEvidence residual_transport lowering_dynamics.sourceCategory
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      (NativeTraceReturnSourcePath
        lowering_dynamics residual_transport n source_descent)
      PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence residual_transport
      lowering_dynamics.sourceCategory n

namespace NativeTraceReturnHardDoorGeometry

variable {PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n : Nat}

/-- The source-path type carried by traces for this native hard-door geometry.
-/
abbrev SourcePath
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n) :
    Type u :=
  NativeTraceReturnSourcePath
    G.lowering_dynamics G.residual_transport n G.source_descent

/-- The native trace-return geometry fills the existing
trace-carried generated-lowering return-certificate domain. -/
def toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n) :
    TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
      G.SourcePath
      PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence n :=
  NativeTraceReturnSourcePath.toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
    (D := G.lowering_dynamics)
    (Residual := G.residual_transport)
    (n := n)
    (S := G.source_descent)
    G.residual_eq_potential
    G.terminal_no_third_sink
    G.step_path

/-- A real traced feasible defect under this geometry carries the active
return packet read from its trace payload. -/
theorem activeReturnPacket
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n)
    {k : Nat}
    (defect :
      TracedFeasibleAtomProjectionDefect
        G.SourcePath
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence G.residual_transport
        G.lowering_dynamics.sourceCategory n (k + 1)) :
    NativeTraceReturnSourcePath.ActiveReturnPacket defect :=
  NativeTraceReturnSourcePath.activeReturnPacket defect

/-- Successor-shell traced feasible defects are impossible because the native
trace payload itself carries the active lower-to-upper return. -/
theorem no_successor_traced_feasible_defect_by_active_return_packet
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n)
    {k : Nat} :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        G.SourcePath
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence G.residual_transport
        G.lowering_dynamics.sourceCategory n (k + 1)) :=
  NativeTraceReturnSourcePath.no_successor_traced_feasible_defect_by_active_return_packet
    (D := G.lowering_dynamics)
    (Residual := G.residual_transport)
    (n := n)
    (S := G.source_descent)
    G.residual_eq_potential

/-- Stable traced feasible defects are impossible through the established
return-certificate domain. -/
theorem no_stable_traced_feasible_defect
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
  G.toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
    |>.no_stable_traced_feasible_atom_projection_defect

/-- Target-shell traced feasible defects are impossible through the established
return-certificate domain. -/
theorem no_target_traced_feasible_defect
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n)
    (target : Nat) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        G.SourcePath
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence G.residual_transport
        G.lowering_dynamics.sourceCategory n target) :=
  G.no_stable_traced_feasible_defect target

/-- Demand-level double-negated atom-realization readout inherited from the
return-certificate domain.

This is still a boundary readout, not an atom-pair producer. -/
theorem not_not_atom_realization_of_traced_feasible_demand
    (G :
      NativeTraceReturnHardDoorGeometry
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n)
    {k : Nat}
    (demand :
      TracedFeasibleRepRepairDemand
        G.SourcePath
        PhaseTrace SigmaTag ProducerTrace
        SourceEvidence G.residual_transport
        G.lowering_dynamics.sourceCategory n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  G.toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
    |>.not_not_atom_realization_of_traced_feasible_demand demand

end NativeTraceReturnHardDoorGeometry


end NativeTraceHardDoor

end RepresentationArithmeticAtomProjectionDefect
