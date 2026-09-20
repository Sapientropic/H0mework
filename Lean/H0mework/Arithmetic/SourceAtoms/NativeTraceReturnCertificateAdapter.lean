import H0mework.Arithmetic.SourceAtoms.NativeTraceActiveReturnCore
import H0mework.Arithmetic.SourceAtoms.TraceCarriedGeneratedLoweringReturnCertificate

/-!
# Native trace return-certificate adapter

This file connects the SU7-free native trace active-return core to the
existing RAAPD return-certificate hard-door domain.

The adapter is intentionally thin: a native trace-return payload supplies the
`trace_returns_lower_to_upper` field, while terminal discharge and residual
step-path compatibility remain explicit source-side inputs.
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

/-- A native trace-return payload family fills the existing
trace-carried generated-lowering return-certificate no-return domain.

This is the bridge from the new SU7-free core to the established downstream
RAAPD hard door. -/
def toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source)
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n)
    (step_path :
      ResidualStepSourcePathCompatibility
        SourceEvidence Residual D.sourceCategory) :
    TraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
      (NativeTraceReturnSourcePath D Residual n S)
      PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence n where
  residual_transport := Residual
  lowering_dynamics := D
  terminal_no_third_sink := terminal
  edge_residual_nonincreasing :=
    D.edgeResidualNonincreasingOfPotentialReadout
      Residual residual_eq_potential
  source_descent := S
  step_path := step_path
  trace_descent :=
    NativeTraceReturnSourcePath.traceDescent
      (D := D) (Residual := Residual) (n := n) (S := S)
      PhaseTrace SigmaTag ProducerTrace
  trace_returns_lower_to_upper := by
    intro _k defect
    exact
      defect.demand.trace.sourcePath.lower_returns_to_upper
        defect.demand.demand.demand

/-- Stable traced feasible defects are impossible through the established
return-certificate domain once traces carry native active-return payloads. -/
theorem no_stable_traced_feasible_defect_via_return_certificate_domain
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source)
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n)
    (step_path :
      ResidualStepSourcePathCompatibility
        SourceEvidence Residual D.sourceCategory) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          (NativeTraceReturnSourcePath D Residual n S)
          PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual D.sourceCategory n k) :=
  (toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
      (D := D) (Residual := Residual) (n := n) (S := S)
      residual_eq_potential terminal step_path)
    |>.no_stable_traced_feasible_atom_projection_defect

/-- Target-shell exclusion through the existing return-certificate domain. -/
theorem no_target_traced_feasible_defect_via_return_certificate_domain
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source)
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n)
    (step_path :
      ResidualStepSourcePathCompatibility
        SourceEvidence Residual D.sourceCategory)
    (target : Nat) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n target) :=
  (toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
      (D := D) (Residual := Residual) (n := n) (S := S)
      residual_eq_potential terminal step_path)
    |>.no_target_traced_feasible_atom_projection_defect target

/-- The demand-level double-negated atom-realization readout inherited from
the existing return-certificate domain.

This theorem is a boundary readout: it does not construct an atom pair; it
records that a traced feasible demand cannot coexist with the source-side
active-return obstruction without double-negating atom realization. -/
theorem not_not_atom_realization_of_traced_feasible_demand_via_return_certificate_domain
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source)
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual D.sourceCategory n)
    (step_path :
      ResidualStepSourcePathCompatibility
        SourceEvidence Residual D.sourceCategory)
    {k : Nat}
    (demand :
      TracedFeasibleRepRepairDemand
        (NativeTraceReturnSourcePath D Residual n S)
        PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual D.sourceCategory n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  (toTraceCarriedGeneratedLoweringReturnCertificateNoReturnDomain
      (D := D) (Residual := Residual) (n := n) (S := S)
      residual_eq_potential terminal step_path)
    |>.not_not_atom_realization_of_traced_feasible_demand demand

end NativeTraceReturnSourcePath


end NativeTraceHardDoor

end RepresentationArithmeticAtomProjectionDefect
