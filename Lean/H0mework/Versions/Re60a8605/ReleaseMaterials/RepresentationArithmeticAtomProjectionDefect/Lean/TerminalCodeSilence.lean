import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Terminal code silence

This module isolates the endpoint-code boundary used by terminal
no-third-sink proofs.

For a terminal traced feasible atom-projection defect, raw endpoint-code
definedness would materialize a shell-zero atom pair through
`AtomicEndpointCodeProjection`.  Therefore the terminal raw code projection
must be silent.  Branch-discharge arguments live in later modules.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Terminal traced feasible defects force terminal raw endpoint-code silence.

If the terminal demand's code projection were defined, faithful endpoint-code
projection plus atom certification would produce a shell-zero atom-pair
realization, contradicting the defect's `noAtomRealization` field. -/
theorem terminal_code_projection_silence_of_traced_feasible_terminal_defect
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (source_descent :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (defect :
      TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :
    Projection.codeProjection.projectCode
        (terminalTracedFeasibleDemandOfSourceDescent
          source_descent step_path trace_descent
          defect.demand).demand.demand.evidence =
      none := by
  by_cases hNone :
      Projection.codeProjection.projectCode
          (terminalTracedFeasibleDemandOfSourceDescent
            source_descent step_path trace_descent
            defect.demand).demand.demand.evidence =
        none
  · exact hNone
  · have hDefined :
        Projection.codeProjection.projectCode
            (terminalTracedFeasibleDemandOfSourceDescent
              source_descent step_path trace_descent
              defect.demand).demand.demand.evidence ≠
          none := hNone
    have hRealized :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = 0 := by
      exact
        atom_pair_realization_of_atomic_code_defined_demand
          Projection
          (terminalTracedFeasibleDemandOfSourceDescent
            source_descent step_path trace_descent
            defect.demand).demand.demand
          hDefined
    exact False.elim (defect.noAtomRealization hRealized)


end RepresentationArithmeticAtomProjectionDefect
