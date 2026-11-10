import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.CodeMediatedSuccessorSteps
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.NoThirdSinkDischarge
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.TerminalBaseSuccessorSteps

/-!
# Source-code formula stable defect exclusion

This module packages a structural sufficient condition:

```text
certified source-code formula
+ terminal no-third-sink
+ bounded source/code successor coherence
-> no stable traced projection defect at the target shell
```

It deliberately does not assume source-code path compatibility.  The theorem
therefore routes through terminal discharge plus bounded successor steps,
rather than through the stronger all-shell source-projection lift.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- A certified source-code formula.

The first law is the residual affine law: whenever the formula returns raw
endpoint codes, their endpoint-code energy agrees with the source residual
energy.  The two certificate laws are the multiplicative certificate
functoriality: projected endpoints carry the arithmetic atom predicate. -/
structure CertifiedSourceCodeFormula
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat)
    (Residual : AdditiveResidualTransportCategory SourceEvidence) where
  projectCode : SourceEvidence -> Option (EndpointCodePair n)
  residual_affine_law :
    ∀ {s : SourceEvidence} {c : EndpointCodePair n},
      projectCode s = some c ->
        EndpointCodePair.energy c = Residual.residualEnergy s
  left_multiplicative_certificate :
    ∀ {s : SourceEvidence} {c : EndpointCodePair n},
      projectCode s = some c -> Atomic c.leftCode
  right_multiplicative_certificate :
    ∀ {s : SourceEvidence} {c : EndpointCodePair n},
      projectCode s = some c -> Atomic c.rightCode

/-- Forget the formula presentation to the existing atomic endpoint-code
projection interface. -/
def CertifiedSourceCodeFormula.toAtomicEndpointCodeProjection
    {Atomic : Nat -> Prop} {SourceEvidence : Type u} {n : Nat}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    (F : CertifiedSourceCodeFormula Atomic SourceEvidence n Residual) :
    AtomicEndpointCodeProjection Atomic SourceEvidence n Residual where
  codeProjection := {
    projectCode := F.projectCode
    code_energy_faithful := F.residual_affine_law
  }
  left_atomic := F.left_multiplicative_certificate
  right_atomic := F.right_multiplicative_certificate

/-- Terminal source-code no-third-sink law for a certified formula.

This is intentionally lighter than `TracedSourceCodeNoThirdSinkDisposition`:
it does not require source-code path compatibility, so it cannot by itself
produce all-shell projection definedness.  It only says that terminal code
silence must resolve as either absorption or projected repair. -/
structure SourceCodeFormulaTerminalNoThirdSink
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Formula :
      CertifiedSourceCodeFormula Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  projected_code_repair :
    ∀ {k : Nat},
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k ->
        Prop
  no_third_sink_on_code_silence :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        Formula.projectCode
            (terminalTracedFeasibleDemandOfSourceDescent
              source_descent step_path trace_descent demand).demand.demand.evidence =
          none ->
        headroom_nonzero ->
          absorbed_static ∨ projected_code_repair demand
  projected_code_repair_defines_projection :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        projected_code_repair demand ->
          Formula.projectCode
              (terminalTracedFeasibleDemandOfSourceDescent
                source_descent step_path trace_descent demand).demand.demand.evidence ≠
            none

/-- A terminal defect for a certified source-code formula induces the pure
two-branch no-third-sink contradiction object. -/
def noThirdSinkDischargeOfSourceCodeFormulaTerminalDefect
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Formula :
      CertifiedSourceCodeFormula Atomic SourceEvidence n Residual}
    (T :
      SourceCodeFormulaTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Formula)
    (defect :
      TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :
    NoThirdSinkDischarge := by
  have hCodeSilence :
      Formula.projectCode
          (terminalTracedFeasibleDemandOfSourceDescent
            T.source_descent T.step_path T.trace_descent
            defect.demand).demand.demand.evidence =
        none := by
    simpa [CertifiedSourceCodeFormula.toAtomicEndpointCodeProjection] using
      (terminal_code_projection_silence_of_traced_feasible_terminal_defect
        (Projection := Formula.toAtomicEndpointCodeProjection)
        T.source_descent T.step_path T.trace_descent defect)
  exact {
    headroom_nonzero := T.headroom_nonzero
    headroom_witness := T.headroom_witness
    absorbed_static := T.absorbed_static
    projected_repair := T.projected_code_repair defect.demand
    no_third_sink := by
      intro hHeadroom
      exact
        T.no_third_sink_on_code_silence
          defect.demand hCodeSilence hHeadroom
    nonzero_forbids_absorbed_static :=
      T.nonzero_forbids_absorbed_static
    defect_forbids_projected_repair := by
      intro hProjected
      exact
        (T.projected_code_repair_defines_projection
          defect.demand hProjected)
        hCodeSilence
  }

/-- Terminal traced feasible projection defects are impossible for a certified
source-code formula satisfying terminal no-third-sink. -/
theorem no_terminal_traced_feasible_defect_of_source_code_formula_terminal
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Formula :
      CertifiedSourceCodeFormula Atomic SourceEvidence n Residual}
    (T :
      SourceCodeFormulaTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Formula) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact
    no_third_sink_discharge_impossible
      (noThirdSinkDischargeOfSourceCodeFormulaTerminalDefect T defect)

/-- Formula-level stable projection-defect domain.

The four important structural fields are:

* `formula.residual_affine_law`;
* `formula.left/right_multiplicative_certificate`;
* `terminal_no_third_sink`;
* `bounded_successor_coherence`.

The last field is code-mediated bounded successor coherence: already-realized
lower shells have source/code anchors whose successor source projects to a
certified endpoint-code pair one residual unit higher. -/
structure SourceCodeFormulaStableProjectionDefectDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n bound : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  formula :
    CertifiedSourceCodeFormula Atomic SourceEvidence n Residual
  terminal_no_third_sink :
    SourceCodeFormulaTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual n Source formula
  bounded_successor_coherence :
    CodeMediatedBoundedPairTransport
      Atomic SourceEvidence Residual n bound
      formula.toAtomicEndpointCodeProjection

/-- Structural theorem: a certified source-code formula with terminal
no-third-sink and bounded successor coherence has no stable traced projection
defect at the target shell. -/
theorem no_traced_feasible_projection_defect_of_source_code_formula_structure
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaStableProjectionDefectDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n bound) := by
  exact
    no_traced_feasible_atom_projection_defect_at_bound_by_terminal_base_successor_steps
      (no_terminal_traced_feasible_defect_of_source_code_formula_terminal
        D.terminal_no_third_sink)
      D.terminal_no_third_sink.source_descent
      D.terminal_no_third_sink.step_path
      D.terminal_no_third_sink.trace_descent
      bound
      (boundedAtomPairRealizationSuccessorStepsOfCodeMediated
        D.bounded_successor_coherence)

/-- Demand-level readout from the structural formula theorem.  This remains a
double-negated realization statement; it is not witness extraction. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_source_code_formula_structure
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaStableProjectionDefectDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound := by
  intro hMissing
  exact
    (no_traced_feasible_projection_defect_of_source_code_formula_structure D)
      ⟨{ demand := demand, noAtomRealization := hMissing }⟩


end RepresentationArithmeticAtomProjectionDefect
