import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.TerminalCodeSilence
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.TracedSourceCodeNoThirdSink

/-!
# No-third-sink discharge

This module factors the sigma-style terminal contradiction into a small pure
Prop object:

```text
headroom_nonzero
absorbed_static or projected_repair
not absorbed_static
not projected_repair
```

It does not add a new producer.  It only makes the terminal discharge law
separate from endpoint-code materialization, so source/code bridge proofs can
show where each branch is ruled out.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Pure two-branch no-third-sink discharge.

This is the abstract terminal shape from the sigma blueprint: nonzero
headroom rules out absorption, while the current defect branch rules out
projection/repair.  The no-third-sink law says there is no third place for the
terminal responsibility to go. -/
structure NoThirdSinkDischarge where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_repair : Prop
  no_third_sink :
    headroom_nonzero -> absorbed_static ∨ projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  defect_forbids_projected_repair :
    ¬ projected_repair

/-- The abstract two-branch discharge is contradictory. -/
theorem no_third_sink_discharge_impossible
    (D : NoThirdSinkDischarge) : False := by
  cases D.no_third_sink D.headroom_witness with
  | inl hAbsorbed =>
      exact
        (D.nonzero_forbids_absorbed_static D.headroom_witness)
        hAbsorbed
  | inr hProjected =>
      exact D.defect_forbids_projected_repair hProjected

/-- A concrete terminal source/code defect induces the pure no-third-sink
discharge.

The only endpoint-code step here is proving terminal code silence: if terminal
raw endpoint-code projection were defined, atom certification would
materialize a shell-zero atom pair and contradict the defect's missing
realization field.  After that, the branch contradiction is pure
no-third-sink discharge. -/
def noThirdSinkDischargeOfSourceCodeTerminalDefect
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (defect :
      TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :
    NoThirdSinkDischarge := by
  have hCodeSilence :
      Projection.codeProjection.projectCode
          (terminalTracedFeasibleDemandOfSourceDescent
            D.source_descent D.step_path D.trace_descent
            defect.demand).demand.demand.evidence =
        none :=
    terminal_code_projection_silence_of_traced_feasible_terminal_defect
      D.source_descent D.step_path D.trace_descent defect
  exact {
    headroom_nonzero := D.headroom_nonzero
    headroom_witness := D.headroom_witness
    absorbed_static := D.absorbed_static
    projected_repair := D.projected_code_repair defect.demand
    no_third_sink := by
      intro hHeadroom
      exact
        D.no_third_sink_on_code_silence
          defect.demand hCodeSilence hHeadroom
    nonzero_forbids_absorbed_static :=
      D.nonzero_forbids_absorbed_static
    defect_forbids_projected_repair := by
      intro hProjected
      exact
        (D.projected_code_repair_defines_projection
          defect.demand hProjected)
        hCodeSilence
  }

/-- Source/code terminal no-third-sink exclusion routed through the abstract
discharge object. -/
theorem no_terminal_traced_feasible_defect_of_source_code_no_third_sink_via_discharge
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact
    no_third_sink_discharge_impossible
      (noThirdSinkDischargeOfSourceCodeTerminalDefect D defect)


end RepresentationArithmeticAtomProjectionDefect
