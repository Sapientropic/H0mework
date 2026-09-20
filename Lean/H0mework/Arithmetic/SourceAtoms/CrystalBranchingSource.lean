import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Rank-one crystal/branching source candidate

This file is a small source-side producer candidate for the active
representation-arithmetic atom projection defect track.

It is not a Goldbach producer.  It does not prove multiplicative atom
certification for endpoint codes.  Instead it makes the source side concrete:
states are residual heights, lowering is `k + 1 -> k`, paths are monotone
height descent, and source traces are transported by the lowering step.

The hard arithmetic part remains explicit in `AtomicEndpointCodeProjection`.
-/

namespace RepresentationArithmeticAtomProjectionDefect
namespace CrystalBranchingSource

/-- Rank-one source-path trace for a single lowering step. -/
structure RankOneSourcePath where
  fromHeight : Nat
  toHeight : Nat

/-- Rank-one phase trace recording the same height movement. -/
structure RankOnePhaseTrace where
  fromHeight : Nat
  toHeight : Nat

/-- Sigma-style tag for the lower residual shell reached by a source step. -/
structure RankOneSigmaTag where
  shell : Nat

/-- Producer trace for the rank-one lowering source. -/
structure RankOneProducerTrace where
  loweredSteps : Nat

/-- Concrete additive residual transport for the rank-one source.

Source evidence is just residual height.  A step from `source` to `target`
means `target + 1 = source`. -/
def rankOneResidualTransport :
    AdditiveResidualTransportCategory Nat where
  residualEnergy := fun height => height
  step := fun source target => target + 1 = source
  step_decreases_one := by
    intro source target hstep
    exact hstep

/-- Concrete source category for rank-one crystal-like lowering.

Every height is feasible; paths are monotone descent in height. -/
def rankOneSourceCategory :
    RepresentationFeasibleCategory Nat where
  feasible := fun _ => True
  path := fun source target => target ≤ source
  path_preserves_feasible := by
    intro source target hPath hFeasible
    trivial

/-- A residual step is a source path in the rank-one source category. -/
theorem rankOneStepPathCompatibility :
    ResidualStepSourcePathCompatibility
      Nat rankOneResidualTransport rankOneSourceCategory := by
  refine { step_is_path := ?_ }
  intro source target hstep
  dsimp [rankOneSourceCategory]
  rw [← hstep]
  exact Nat.le_succ target

/-- Rank-one source descent lowers a demand at shell `k + 1` to shell `k`. -/
def rankOneSourceDemandOneStepDescent (n : Nat) :
    SourceDemandOneStepDescent Nat rankOneResidualTransport n where
  lowerEvidence := fun {k} _demand => k
  step_to_lower := by
    intro k demand
    dsimp [rankOneResidualTransport]
    exact demand.residual_eq.symm

/-- Trace descent for the rank-one source lowering step. -/
def rankOneTraceDescent (n : Nat) :
    SourceRepairTraceDescent
      RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
      Nat rankOneResidualTransport rankOneSourceCategory n where
  lowerTrace := by
    intro k demand
    exact {
      sourcePath := {
        fromHeight := demand.demand.demand.evidence
        toHeight := k
      }
      phaseTrace := {
        fromHeight := k + 1
        toHeight := k
      }
      sigmaTag := {
        shell := k
      }
      producerTrace := {
        loweredSteps := 1
      }
    }

/-- Concrete traced feasible demand for a rank-one source height.

This is useful for future source instances: the evidence is the residual
height itself, while trace records where the demand came from. -/
def tracedDemandOfHeight
    (n k : Nat) :
    TracedFeasibleRepRepairDemand
      RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
      Nat rankOneResidualTransport rankOneSourceCategory n k where
  demand := {
    demand := {
      evidence := k
      residual_eq := rfl
    }
    feasible := by
      trivial
  }
  trace := {
    sourcePath := {
      fromHeight := k
      toHeight := k
    }
    phaseTrace := {
      fromHeight := k
      toHeight := k
    }
    sigmaTag := {
      shell := k
    }
    producerTrace := {
      loweredSteps := 0
    }
  }

/-- Rank-one crystal/branching endpoint-code projection candidate.

The source category is concrete.  The arithmetic gate is still explicit:
`code_projection` must certify multiplicative atomhood of projected endpoint
codes.  Therefore this structure is not a hidden prime-pair premise unless a
future instance fills `code_projection` by smuggling in coverage. -/
structure RankOneCrystalCodeProjectionCandidate
    (Atomic : Nat -> Prop) (n : Nat) where
  code_projection :
    AtomicEndpointCodeProjection
      Atomic Nat n rankOneResidualTransport
  code_defined_lifts_along_path :
    ∀ {source target : Nat},
      rankOneSourceCategory.path source target ->
        code_projection.codeProjection.projectCode target ≠ none ->
          code_projection.codeProjection.projectCode source ≠ none
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_code_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag
          RankOneProducerTrace Nat rankOneResidualTransport
          rankOneSourceCategory n k),
        code_projection.codeProjection.projectCode
            (terminalTracedFeasibleDemandOfSourceDescent
              (rankOneSourceDemandOneStepDescent n)
              rankOneStepPathCompatibility
              (rankOneTraceDescent n)
              demand).demand.demand.evidence =
          none ->
            absorbed_static

/-- Rank-one source path compatibility for endpoint-code definedness. -/
theorem rankOneCodeProjectionPathCompatibility
    {Atomic : Nat -> Prop} {n : Nat}
    (C : RankOneCrystalCodeProjectionCandidate Atomic n) :
    SourceCodeProjectionPathCompatibility
      Atomic Nat rankOneResidualTransport n rankOneSourceCategory
      C.code_projection := by
  exact {
    code_projection_defined_lifts_along_path :=
      C.code_defined_lifts_along_path
  }

/-- The rank-one source candidate induces the traced feasible nonabsorbed lift
domain used by the general defect theory. -/
def rankOneTracedCodeNonabsorbedLiftDomain
    {Atomic : Nat -> Prop} {n : Nat}
    (C : RankOneCrystalCodeProjectionCandidate Atomic n) :
    TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
      RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
      Atomic Nat rankOneResidualTransport n rankOneSourceCategory
      C.code_projection where
  source_descent := rankOneSourceDemandOneStepDescent n
  step_path := rankOneStepPathCompatibility
  trace_descent := rankOneTraceDescent n
  path_compatibility := rankOneCodeProjectionPathCompatibility C
  absorbed_static := C.absorbed_static
  headroom_nonzero := C.headroom_nonzero
  headroom_witness := C.headroom_witness
  nonzero_forbids_absorbed_static :=
    C.nonzero_forbids_absorbed_static
  terminal_code_projection_undefined_absorbs :=
    C.terminal_code_projection_undefined_absorbs

/-- A rank-one crystal/branching source candidate realizes the atom-pair shell
for every traced feasible demand once endpoint-code atom certification and
terminal nonabsorption are supplied.

This theorem is not a finite endpoint search.  The endpoint-code projection
and multiplicative atom certification remain explicit fields of `C`. -/
theorem atom_pair_realization_of_rank_one_crystal_code_candidate
    {Atomic : Nat -> Prop} {n k : Nat}
    (C : RankOneCrystalCodeProjectionCandidate Atomic n)
    (demand :
      TracedFeasibleRepRepairDemand
        RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
        Nat rankOneResidualTransport rankOneSourceCategory n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_traced_feasible_source_code_projection_path_nonabsorbed_lift
    (rankOneTracedCodeNonabsorbedLiftDomain C)
    demand

/-- The rank-one source candidate rules out traced feasible atom-projection
defects for every shell. -/
theorem no_traced_feasible_defect_of_rank_one_crystal_code_candidate
    {Atomic : Nat -> Prop} {n k : Nat}
    (C : RankOneCrystalCodeProjectionCandidate Atomic n) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        RankOneSourcePath RankOnePhaseTrace RankOneSigmaTag RankOneProducerTrace
        Atomic Nat rankOneResidualTransport rankOneSourceCategory n k) :=
  not_traced_feasible_defect_of_source_code_projection_path_nonabsorbed_lift
    (rankOneTracedCodeNonabsorbedLiftDomain C)
    (tracedDemandOfHeight n k)

/-- Demand-level version specialized to the canonical demand at height `k`. -/
theorem atom_pair_realization_of_rank_one_height
    {Atomic : Nat -> Prop} {n k : Nat}
    (C : RankOneCrystalCodeProjectionCandidate Atomic n) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_rank_one_crystal_code_candidate
    C (tracedDemandOfHeight n k)

/-- Shell-zero readout forced by a rank-one code-projection candidate.

This is a hardness warning, not a new producer theorem: a candidate that fills
the endpoint-code atom certification and terminal nonabsorption fields already
realizes the zero residual shell. -/
theorem atom_pair_realization_zero_of_rank_one_crystal_code_candidate
    {Atomic : Nat -> Prop} {n : Nat}
    (C : RankOneCrystalCodeProjectionCandidate Atomic n) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = 0 :=
  atom_pair_realization_of_rank_one_height (n := n) (k := 0) C

/-- Nat multiplicative-atom specialization of the shell-zero hardness readout.

For the intended multiplicative atom filter, a rank-one candidate at fiber `n`
already entails a shell-zero atom-pair realization for `2 * n`.  Therefore the
candidate construction itself must earn atom certification and nonabsorption
from representation dynamics; otherwise it is only hiding the arithmetic
coverage problem. -/
theorem nat_atom_pair_realization_zero_of_rank_one_crystal_code_candidate
    {n : Nat}
    (C : RankOneCrystalCodeProjectionCandidate NatMultiplicativelyAtomic n) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = 0 :=
  atom_pair_realization_zero_of_rank_one_crystal_code_candidate C

/-- Uniform rank-one candidates for the Nat multiplicative atom filter imply
uniform shell-zero atom-pair realization.

This theorem is deliberately phrased as a rejection test: a proposed uniform
rank-one construction has Goldbach-strength content already, so it cannot be
accepted as an upstream source producer unless its endpoint atom certification
is proved independently of prime-pair coverage. -/
theorem nat_atom_pair_zero_realization_of_uniform_rank_one_candidates
    (Candidate : ∀ n : Nat,
      RankOneCrystalCodeProjectionCandidate NatMultiplicativelyAtomic n) :
    ∀ n : Nat,
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0 := by
  intro n
  exact
    nat_atom_pair_realization_zero_of_rank_one_crystal_code_candidate
      (Candidate n)

/-- Rejection-test alias for the uniform rank-one Nat atom candidate.

The name records the intended reading: proving such a uniform candidate is at
least Goldbach-strength at shell zero. -/
theorem rank_one_candidate_atom_certification_is_goldbach_strength
    (Candidate : ∀ n : Nat,
      RankOneCrystalCodeProjectionCandidate NatMultiplicativelyAtomic n) :
    ∀ n : Nat,
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0 :=
  nat_atom_pair_zero_realization_of_uniform_rank_one_candidates Candidate


end CrystalBranchingSource
end RepresentationArithmeticAtomProjectionDefect
