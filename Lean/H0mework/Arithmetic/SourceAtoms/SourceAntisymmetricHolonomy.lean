import H0mework.Arithmetic.SourceAtoms.SourceHolonomyLoop
import H0mework.Arithmetic.SourceAtoms.CrystalBranchingSource

/-!
# Source antisymmetric holonomy

This file lowers the source-holonomy target one step further.

`SourceHolonomyLoop.lean` asks for a source path loop plus an explicit closed
endpoint equality.  Here the equality is derived from source-category
antisymmetry:

```text
source -> target path
target -> source path
source path antisymmetry
strict residual drop
-> forbidden source closed strict residual holonomy
```

The rank-one source category is included as a sanity check: its monotone
height paths are antisymmetric, so it cannot produce this holonomy pattern.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Source path antisymmetry.

This is the categorical condition that a two-way source path loop is already
closed at the evidence level.  Poset-like GT / crystal / branching sources
should aim to prove this or explicitly explain why their holonomy is genuinely
cyclic rather than antisymmetric. -/
structure SourcePathAntisymmetry
    (SourceEvidence : Type u)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  closes :
    ∀ {source target : SourceEvidence},
      Source.path source target ->
        Source.path target source ->
          target = source

/-- Source-category pre-holonomy loop with strict residual drop.

Unlike `SourceClosedStrictResidualHolonomyAt`, this does not carry a closed
endpoint equality.  The equality is meant to be derived from source path
antisymmetry. -/
structure SourcePreClosedStrictResidualHolonomyAt
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (source : SourceEvidence) where
  target : SourceEvidence
  source_to_target : Source.path source target
  target_to_source : Source.path target source
  residual_drops :
    Residual.residualEnergy target < Residual.residualEnergy source

/-- Under source path antisymmetry, a pre-holonomy loop becomes a closed
strict residual holonomy loop. -/
def sourceClosedStrictResidualHolonomyAtOfAntisymmetricPreLoop
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {source : SourceEvidence}
    (A : SourcePathAntisymmetry SourceEvidence Source)
    (H :
      SourcePreClosedStrictResidualHolonomyAt
        SourceEvidence Residual Source source) :
    SourceClosedStrictResidualHolonomyAt
      SourceEvidence Residual Source source where
  target := H.target
  source_to_target := H.source_to_target
  target_to_source := H.target_to_source
  closes := A.closes H.source_to_target H.target_to_source
  residual_drops := H.residual_drops

/-- An antisymmetric source-category pre-holonomy loop with strict residual
drop is impossible. -/
theorem no_source_preclosed_strict_residual_holonomy_at_of_antisymmetry
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {source : SourceEvidence}
    (A : SourcePathAntisymmetry SourceEvidence Source) :
    ¬ Nonempty
      (SourcePreClosedStrictResidualHolonomyAt
        SourceEvidence Residual Source source) := by
  intro h
  rcases h with ⟨H⟩
  exact
    no_source_closed_strict_residual_holonomy_at
      ⟨sourceClosedStrictResidualHolonomyAtOfAntisymmetricPreLoop A H⟩

/-- Feasible defect-to-antisymmetric-source-loop map.

This is one level below the source-loop map: every defect generates a two-way
source path loop with strict residual drop, while source path antisymmetry
turns that loop into a closed strict residual holonomy. -/
structure FeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  path_antisymmetry : SourcePathAntisymmetry SourceEvidence Source
  source_preloop_at :
    ∀ {k : Nat}
      (defect :
        FeasibleAtomProjectionDefect
          Atomic SourceEvidence Residual Source n k),
        SourcePreClosedStrictResidualHolonomyAt
          SourceEvidence Residual Source defect.demand.demand.evidence

/-- A feasible antisymmetric source-loop map generates the source-loop map.
-/
def feasibleSourceLoopMapOfAntisymmetricHolonomyMap
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      FeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        Atomic SourceEvidence Residual Source n) :
    FeasibleAtomProjectionDefectToSourceHolonomyLoopMap
      Atomic SourceEvidence Residual Source n where
  source_loop_at := fun defect =>
    sourceClosedStrictResidualHolonomyAtOfAntisymmetricPreLoop
      M.path_antisymmetry
      (M.source_preloop_at defect)

/-- Feasible antisymmetric source-loop maps exclude feasible defects. -/
theorem no_feasible_atom_projection_defect_of_antisymmetric_source_holonomy_map
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      FeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (FeasibleAtomProjectionDefect
          Atomic SourceEvidence Residual Source n k) :=
  no_feasible_atom_projection_defect_of_source_holonomy_loop_map
    (feasibleSourceLoopMapOfAntisymmetricHolonomyMap M)

/-- Demand-level feasible consequence of an antisymmetric source-loop map. -/
theorem not_not_atom_realization_of_feasible_demand_by_antisymmetric_source_holonomy_map
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (M :
      FeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        Atomic SourceEvidence Residual Source n)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_feasible_demand_by_source_holonomy_loop_map
    (feasibleSourceLoopMapOfAntisymmetricHolonomyMap M)
    demand

/-- Traced feasible defect-to-antisymmetric-source-loop map. -/
structure TracedFeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  path_antisymmetry : SourcePathAntisymmetry SourceEvidence Source
  source_preloop_at :
    ∀ {k : Nat}
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k),
        SourcePreClosedStrictResidualHolonomyAt
          SourceEvidence Residual Source defect.demand.demand.demand.evidence

/-- A traced antisymmetric source-loop map generates the traced source-loop
map. -/
def tracedSourceLoopMapOfAntisymmetricHolonomyMap
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      TracedFeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    TracedFeasibleAtomProjectionDefectToSourceHolonomyLoopMap
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  source_loop_at := fun defect =>
    sourceClosedStrictResidualHolonomyAtOfAntisymmetricPreLoop
      M.path_antisymmetry
      (M.source_preloop_at defect)

/-- Traced antisymmetric source-loop maps exclude traced feasible defects. -/
theorem no_traced_feasible_atom_projection_defect_of_antisymmetric_source_holonomy_map
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      TracedFeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_of_source_holonomy_loop_map
    (tracedSourceLoopMapOfAntisymmetricHolonomyMap M)

/-- Demand-level traced consequence of an antisymmetric source-loop map. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_antisymmetric_source_holonomy_map
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (M :
      TracedFeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_source_holonomy_loop_map
    (tracedSourceLoopMapOfAntisymmetricHolonomyMap M)
    demand

/-- Active produced demand plus a traced antisymmetric source-loop map rules
out the active missing-realization branch. -/
theorem not_not_atom_realization_of_active_produced_demand_by_antisymmetric_source_holonomy_map
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (M :
      TracedFeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_antisymmetric_source_holonomy_map
    M (P.produce hActive)

/-- Defect-exclusion form for active produced demands using traced
antisymmetric source-loop maps. -/
theorem no_traced_feasible_defect_of_active_produced_demand_by_antisymmetric_source_holonomy_map
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (M :
      TracedFeasibleAtomProjectionDefectToAntisymmetricSourceHolonomyMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (_hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_of_antisymmetric_source_holonomy_map
    M k

namespace CrystalBranchingSource

/-- Rank-one monotone source paths are antisymmetric. -/
theorem rankOneSourcePathAntisymmetry :
    SourcePathAntisymmetry Nat rankOneSourceCategory := by
  refine { closes := ?_ }
  intro source target hForward hBackward
  exact Nat.le_antisymm hForward hBackward

/-- Rank-one monotone height source cannot contain an antisymmetric preclosed
strict residual holonomy loop. -/
theorem no_rank_one_source_preclosed_strict_residual_holonomy_at
    (source : Nat) :
    ¬ Nonempty
      (SourcePreClosedStrictResidualHolonomyAt
        Nat rankOneResidualTransport rankOneSourceCategory source) :=
  no_source_preclosed_strict_residual_holonomy_at_of_antisymmetry
    rankOneSourcePathAntisymmetry

end CrystalBranchingSource


end RepresentationArithmeticAtomProjectionDefect
