import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.SourceCodeFormulaStableDefect
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.RankOneCompositeDynamicsToy

/-!
# Source-code formula positive steps

This file weakens the formula-level successor-coherence obligation from
code-mediated pair transport to positive realization successor steps:

```text
realization at k -> realization at k+1
```

That interface is enough for terminal-base finite descent, and it is easier to
fill from genuine source dynamics.  The rank-one composite toy below
instantiates the weakened formula domain with a total source-code formula and
explicit composite factorization certificates.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Shell-zero realization plus bounded positive successor steps extracts an
atom-pair realization at the target shell.

This is the constructive companion to the defect-exclusion theorem: the
positive-step interface is not only a way to descend gaps by contraposition;
with a terminal witness, it transports actual realizations upward. -/
theorem atom_pair_realization_at_bound_of_zero_and_successor_steps
    {Atomic : Nat -> Prop} {n : Nat}
    (hZero :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∀ bound : Nat,
      BoundedAtomPairRealizationSuccessorSteps Atomic n bound ->
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = bound := by
  intro bound
  induction bound with
  | zero =>
      intro _steps
      exact hZero
  | succ k ih =>
      intro steps
      have hPrev :
          ∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k :=
        ih
          (boundedAtomPairRealizationSuccessorStepsRestrict
            steps (Nat.le_succ k))
      exact
        steps.lift_realization
          (k := k) (Nat.lt_succ_self k) hPrev

/-- Factorized readout for the positive-step witness extraction theorem. -/
theorem factorized_atom_pair_realization_at_bound_of_zero_and_successor_steps
    {Atomic : Nat -> Prop} {n bound : Nat}
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    (hZero :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0)
    (steps : BoundedAtomPairRealizationSuccessorSteps Atomic n bound) :
    FactorizedAtomPairRealization Atomic F n bound := by
  rcases
    atom_pair_realization_at_bound_of_zero_and_successor_steps
      hZero bound steps with
    ⟨p, hEnergy⟩
  exact factorizedAtomPairRealizationOfPair F p hEnergy

/-- Formula-level domain whose successor coherence is the positive
realization-step interface, not the stronger code-mediated pair transport
interface.

The structural fields are still the intended four:

* residual affine readout, inside `formula`;
* multiplicative endpoint certificates, inside `formula`;
* terminal no-third-sink;
* bounded positive successor coherence.
-/
structure SourceCodeFormulaPositiveStepDomain
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
  bounded_successor_steps :
    BoundedAtomPairRealizationSuccessorSteps Atomic n bound

/-- Formula-level positive extraction domain.

This adds a terminal shell-zero witness to the positive-step domain, upgrading
the conclusion from double-negated realization / defect exclusion to actual
atom-pair witness extraction at the target shell. -/
structure SourceCodeFormulaPositiveExtractionDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n bound : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  positive_domain :
    SourceCodeFormulaPositiveStepDomain
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual n bound Source
  terminal_zero_realization :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = 0

/-- Formula-level positive extraction domain where the terminal shell witness
is not supplied directly.  Instead it is materialized from the formula's raw
endpoint-code projection at a terminal traced demand. -/
structure SourceCodeFormulaPositiveMaterializationExtractionDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n bound : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  positive_domain :
    SourceCodeFormulaPositiveStepDomain
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual n bound Source
  terminal_demand :
    TracedFeasibleRepRepairDemand
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n 0
  terminal_code_defined :
    positive_domain.formula.projectCode
        terminal_demand.demand.demand.evidence ≠ none

/-- Terminal raw-code materialization gives the shell-zero atom-pair witness
used by positive extraction. -/
theorem terminal_zero_realization_of_source_code_formula_positive_materialization
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaPositiveMaterializationExtractionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = 0 :=
  atom_pair_realization_of_atomic_code_defined_demand
    D.positive_domain.formula.toAtomicEndpointCodeProjection
    D.terminal_demand.demand.demand
    (by
      simpa [CertifiedSourceCodeFormula.toAtomicEndpointCodeProjection]
        using D.terminal_code_defined)

/-- Forget terminal materialization to the earlier positive extraction domain.
-/
def sourceCodeFormulaPositiveExtractionDomainOfMaterialization
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaPositiveMaterializationExtractionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source) :
    SourceCodeFormulaPositiveExtractionDomain
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual n bound Source where
  positive_domain := D.positive_domain
  terminal_zero_realization :=
    terminal_zero_realization_of_source_code_formula_positive_materialization D

/-- Actual target-shell witness extraction from a formula-level positive
extraction domain. -/
theorem atom_pair_realization_of_source_code_formula_positive_extraction
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaPositiveExtractionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  atom_pair_realization_at_bound_of_zero_and_successor_steps
    D.terminal_zero_realization
    bound D.positive_domain.bounded_successor_steps

/-- Factorized target-shell witness extraction from the formula-level positive
extraction domain. -/
theorem factorized_atom_pair_realization_of_source_code_formula_positive_extraction
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    (D :
      SourceCodeFormulaPositiveExtractionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source) :
    FactorizedAtomPairRealization Atomic F n bound :=
  factorized_atom_pair_realization_at_bound_of_zero_and_successor_steps
    F D.terminal_zero_realization D.positive_domain.bounded_successor_steps

/-- Actual target-shell witness extraction from terminal code materialization
and positive successor steps. -/
theorem atom_pair_realization_of_source_code_formula_positive_materialization
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaPositiveMaterializationExtractionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  atom_pair_realization_of_source_code_formula_positive_extraction
    (sourceCodeFormulaPositiveExtractionDomainOfMaterialization D)

/-- Factorized target-shell witness extraction from terminal code
materialization and positive successor steps. -/
theorem factorized_atom_pair_realization_of_source_code_formula_positive_materialization
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    (D :
      SourceCodeFormulaPositiveMaterializationExtractionDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n bound Source) :
    FactorizedAtomPairRealization Atomic F n bound :=
  factorized_atom_pair_realization_of_source_code_formula_positive_extraction
    F (sourceCodeFormulaPositiveExtractionDomainOfMaterialization D)

/-- Formula-level defect exclusion using the weaker positive-step coherence
field. -/
theorem no_traced_feasible_projection_defect_of_source_code_formula_positive_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaPositiveStepDomain
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
      D.bounded_successor_steps

/-- Demand-level readout from formula-level terminal discharge plus bounded
positive successor steps. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_source_code_formula_positive_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (D :
      SourceCodeFormulaPositiveStepDomain
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
    (no_traced_feasible_projection_defect_of_source_code_formula_positive_steps D)
      ⟨{ demand := demand, noAtomRealization := hMissing }⟩

namespace CrystalBranchingSource
namespace RankOneCompositeDynamicsToy

open CompositeSourceFamily

/-- Rank-one composite source-code formula packaged in the formula-level
interface. -/
def rankOneCompositeCertifiedFormula
    (n : Nat) (hn : 6 ≤ n) :
    CertifiedSourceCodeFormula
      CompositeAtom Nat n rankOneResidualTransport where
  projectCode := fun height =>
    some (rankOneCompositeEndpointCode n height)
  residual_affine_law := by
    intro height code hproject
    cases hproject
    exact rankOneCompositeEndpointCode_energy n height hn
  left_multiplicative_certificate := by
    intro height code hproject
    cases hproject
    exact rankOneCompositeEndpointCode_left_atomic n height
  right_multiplicative_certificate := by
    intro height code hproject
    cases hproject
    exact rankOneCompositeEndpointCode_right_atomic n height hn

/-- Terminal no-third-sink for the rank-one composite formula.

The terminal projected branch is raw code materialization at the terminal
source evidence.  It is forced because the source-code formula is total. -/
def rankOneCompositeFormulaTerminalNoThirdSink
    (n : Nat) (hn : 6 ≤ n) :
    SourceCodeFormulaTerminalNoThirdSink
      RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
      CompositeAtom Nat rankOneResidualTransport n rankOneSourceCategory
      (rankOneCompositeCertifiedFormula n hn) where
  source_descent := rankOneSourceDemandOneStepDescent n
  step_path := rankOneStepPathCompatibility
  trace_descent := rankOneTraceDescent n
  absorbed_static := False
  headroom_nonzero := True
  headroom_witness := trivial
  nonzero_forbids_absorbed_static := by
    intro _ hAbsorbed
    exact hAbsorbed
  projected_code_repair := by
    intro k demand
    exact
      (rankOneCompositeCertifiedFormula n hn).projectCode
          (terminalTracedFeasibleDemandOfSourceDescent
            (rankOneSourceDemandOneStepDescent n)
            rankOneStepPathCompatibility
            (rankOneTraceDescent n)
            demand).demand.demand.evidence ≠
        none
  no_third_sink_on_code_silence := by
    intro k demand _hNone _hHeadroom
    right
    dsimp [rankOneCompositeCertifiedFormula]
    simp
  projected_code_repair_defines_projection := by
    intro k demand hProjected
    exact hProjected

/-- Bounded positive successor steps supplied by the rank-one composite source
formula.  The existing realization input is only used as the step premise; the
successor realization itself comes from the source formula at height `k + 1`.
-/
theorem rankOneCompositePositiveSuccessorSteps
    (n bound : Nat) (hn : 6 ≤ n) :
    BoundedAtomPairRealizationSuccessorSteps CompositeAtom n bound where
  lift_realization := by
    intro k _hk _hRealized
    exact rankOneCompositeAtomPairRealizationOfHeight n (k + 1) hn

/-- Rank-one composite instance of the weakened formula-level domain. -/
def rankOneCompositePositiveStepFormulaDomain
    (n bound : Nat) (hn : 6 ≤ n) :
    SourceCodeFormulaPositiveStepDomain
      RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
      CompositeAtom Nat rankOneResidualTransport n bound
      rankOneSourceCategory where
  formula := rankOneCompositeCertifiedFormula n hn
  terminal_no_third_sink :=
    rankOneCompositeFormulaTerminalNoThirdSink n hn
  bounded_successor_steps :=
    rankOneCompositePositiveSuccessorSteps n bound hn

/-- Rank-one composite instance of the formula-level positive extraction
domain. -/
def rankOneCompositePositiveExtractionDomain
    (n bound : Nat) (hn : 6 ≤ n) :
    SourceCodeFormulaPositiveExtractionDomain
      RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
      CompositeAtom Nat rankOneResidualTransport n bound
      rankOneSourceCategory where
  positive_domain :=
    rankOneCompositePositiveStepFormulaDomain n bound hn
  terminal_zero_realization :=
    rankOneCompositeAtomPairRealizationOfHeight n 0 hn

/-- Rank-one composite positive extraction with the terminal witness
materialized from raw endpoint-code projection, rather than supplied as a
separate atom-pair witness. -/
def rankOneCompositePositiveMaterializationExtractionDomain
    (n bound : Nat) (hn : 6 ≤ n) :
    SourceCodeFormulaPositiveMaterializationExtractionDomain
      RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
      CompositeAtom Nat rankOneResidualTransport n bound
      rankOneSourceCategory where
  positive_domain :=
    rankOneCompositePositiveStepFormulaDomain n bound hn
  terminal_demand := tracedDemandOfHeight n 0
  terminal_code_defined := by
    dsimp [
      rankOneCompositePositiveStepFormulaDomain,
      rankOneCompositeCertifiedFormula
    ]
    simp

/-- The weakened formula-level bridge gives the expected demand-level readout
for the rank-one composite source dynamics. -/
theorem not_not_rankOneCompositeFormulaRealizationByPositiveSteps
    (n height : Nat) (hn : 6 ≤ n) :
    ¬¬ ∃ p : ArithmeticAtomPair CompositeAtom n,
      ArithmeticAtomPair.energy p = height := by
  exact
    not_not_atom_realization_of_traced_feasible_demand_by_source_code_formula_positive_steps
      (rankOneCompositePositiveStepFormulaDomain n height hn)
      (tracedDemandOfHeight n height)

/-- The same weakened formula-level bridge excludes traced feasible defects
for the rank-one composite source dynamics. -/
theorem no_rankOneCompositeFormulaDefectByPositiveSteps
    (n height : Nat) (hn : 6 ≤ n) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
        CompositeAtom Nat rankOneResidualTransport rankOneSourceCategory
        n height) :=
  no_traced_feasible_projection_defect_of_source_code_formula_positive_steps
    (rankOneCompositePositiveStepFormulaDomain n height hn)

/-- Positive formula-level extraction gives an actual factorized atom-pair
witness for the rank-one composite source dynamics. -/
theorem factorizedRankOneCompositeFormulaRealizationByPositiveExtraction
    (n height : Nat) (hn : 6 ≤ n) :
    FactorizedAtomPairRealization
      CompositeAtom compositeFactorizationCategory n height :=
  factorized_atom_pair_realization_of_source_code_formula_positive_extraction
    compositeFactorizationCategory
    (rankOneCompositePositiveExtractionDomain n height hn)

/-- Terminal materialization plus positive formula steps extracts the
factorized rank-one composite target witness. -/
theorem factorizedRankOneCompositeFormulaRealizationByTerminalMaterialization
    (n height : Nat) (hn : 6 ≤ n) :
    FactorizedAtomPairRealization
      CompositeAtom compositeFactorizationCategory n height :=
  factorized_atom_pair_realization_of_source_code_formula_positive_materialization
    compositeFactorizationCategory
    (rankOneCompositePositiveMaterializationExtractionDomain n height hn)


end RankOneCompositeDynamicsToy
end CrystalBranchingSource

end RepresentationArithmeticAtomProjectionDefect
