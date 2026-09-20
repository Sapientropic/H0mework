import H0mework.Arithmetic.ProjectionDefect.DefectToHolonomyMap

/-!
# Source holonomy loop

This file inserts the source-category layer into the holonomy route.

`DefectToHolonomyMap.lean` targets a closed strict residual holonomy based at a
defect's source evidence.  Here we refine that target with source paths:

```text
source path loop
+ closed endpoint equality
+ strict residual drop
-> closed strict residual holonomy
```

The equality still supplies the elementary contradiction, but the loop data
keeps the future source theorem tied to representation / GT / crystal /
branching paths rather than to a bare evidence equality.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Source-category closed holonomy loop with strict residual drop.

The source path data records that the holonomy is generated inside the
representation/source category.  The `closes` field records that the loop
returns to the same source evidence, which is what makes a strict Nat-valued
residual drop impossible. -/
structure SourceClosedStrictResidualHolonomyAt
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (source : SourceEvidence) where
  target : SourceEvidence
  source_to_target : Source.path source target
  target_to_source : Source.path target source
  closes : target = source
  residual_drops :
    Residual.residualEnergy target < Residual.residualEnergy source

/-- The target of a source holonomy loop is feasible whenever the base source
is feasible. -/
theorem target_feasible_of_source_closed_strict_residual_holonomy_at
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {source : SourceEvidence}
    (H :
      SourceClosedStrictResidualHolonomyAt
        SourceEvidence Residual Source source)
    (hSource : Source.feasible source) :
    Source.feasible H.target :=
  Source.path_preserves_feasible H.source_to_target hSource

/-- Forget source-path loop data and retain the fixed-base strict residual
holonomy. -/
def closedStrictResidualHolonomyAtOfSourceLoop
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {source : SourceEvidence}
    (H :
      SourceClosedStrictResidualHolonomyAt
        SourceEvidence Residual Source source) :
    ClosedStrictResidualHolonomyAt SourceEvidence Residual source where
  target := H.target
  closes := H.closes
  residual_drops := H.residual_drops

/-- A source-category closed strict residual loop is impossible. -/
theorem no_source_closed_strict_residual_holonomy_at
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {source : SourceEvidence} :
    ¬ Nonempty
      (SourceClosedStrictResidualHolonomyAt
        SourceEvidence Residual Source source) := by
  intro h
  rcases h with ⟨H⟩
  exact
    no_closed_strict_residual_holonomy_at
      ⟨closedStrictResidualHolonomyAtOfSourceLoop H⟩

/-- Feasible defect-to-source-loop map.

This is one level below `FeasibleAtomProjectionDefectToHolonomyMap`: every
feasible projection defect must generate a source-category closed strict
residual loop based at that defect's evidence. -/
structure FeasibleAtomProjectionDefectToSourceHolonomyLoopMap
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  source_loop_at :
    ∀ {k : Nat}
      (defect :
        FeasibleAtomProjectionDefect
          Atomic SourceEvidence Residual Source n k),
        SourceClosedStrictResidualHolonomyAt
          SourceEvidence Residual Source defect.demand.demand.evidence

/-- A feasible source-loop map generates the defect-to-holonomy map. -/
def feasibleDefectToHolonomyMapOfSourceLoopMap
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      FeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        Atomic SourceEvidence Residual Source n) :
    FeasibleAtomProjectionDefectToHolonomyMap
      Atomic SourceEvidence Residual Source n where
  holonomy_at := fun defect =>
    closedStrictResidualHolonomyAtOfSourceLoop
      (M.source_loop_at defect)

/-- Feasible source-loop maps exclude feasible atom-projection defects. -/
theorem no_feasible_atom_projection_defect_of_source_holonomy_loop_map
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      FeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (FeasibleAtomProjectionDefect
          Atomic SourceEvidence Residual Source n k) :=
  no_feasible_atom_projection_defect_of_defect_to_holonomy_map
    (feasibleDefectToHolonomyMapOfSourceLoopMap M)

/-- Demand-level feasible consequence of a source-loop map. -/
theorem not_not_atom_realization_of_feasible_demand_by_source_holonomy_loop_map
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (M :
      FeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        Atomic SourceEvidence Residual Source n)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_feasible_demand_by_defect_to_holonomy_map
    (feasibleDefectToHolonomyMapOfSourceLoopMap M)
    demand

/-- Traced feasible defect-to-source-loop map.

The map acts on the traced defect itself, so a future source theorem cannot
discard sourcePath / phaseTrace / sigmaTag / producerTrace before generating
the holonomy loop. -/
structure TracedFeasibleAtomProjectionDefectToSourceHolonomyLoopMap
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  source_loop_at :
    ∀ {k : Nat}
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k),
        SourceClosedStrictResidualHolonomyAt
          SourceEvidence Residual Source defect.demand.demand.demand.evidence

/-- A traced source-loop map generates the traced defect-to-holonomy map. -/
def tracedDefectToHolonomyMapOfSourceLoopMap
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      TracedFeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    TracedFeasibleAtomProjectionDefectToHolonomyMap
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  holonomy_at := fun defect =>
    closedStrictResidualHolonomyAtOfSourceLoop
      (M.source_loop_at defect)

/-- Traced source-loop maps exclude traced feasible atom-projection defects.
-/
theorem no_traced_feasible_atom_projection_defect_of_source_holonomy_loop_map
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (M :
      TracedFeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_of_defect_to_holonomy_map
    (tracedDefectToHolonomyMapOfSourceLoopMap M)

/-- Demand-level traced consequence of a source-loop map. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_source_holonomy_loop_map
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (M :
      TracedFeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_defect_to_holonomy_map
    (tracedDefectToHolonomyMapOfSourceLoopMap M)
    demand

/-- Active produced demand plus traced source-loop map rules out the active
missing-realization branch without returning an endpoint witness. -/
theorem not_not_atom_realization_of_active_produced_demand_by_source_holonomy_loop_map
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
      TracedFeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_source_holonomy_loop_map
    M (P.produce hActive)

/-- Defect-exclusion form for active produced demands using traced source-loop
maps. -/
theorem no_traced_feasible_defect_of_active_produced_demand_by_source_holonomy_loop_map
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
      TracedFeasibleAtomProjectionDefectToSourceHolonomyLoopMap
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (_hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_of_source_holonomy_loop_map M k


end RepresentationArithmeticAtomProjectionDefect
