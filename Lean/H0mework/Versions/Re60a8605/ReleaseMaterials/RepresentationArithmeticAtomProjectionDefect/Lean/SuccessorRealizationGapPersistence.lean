import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Successor realization gap persistence

This module exposes the lowered shape of `gap_descends` as a first-class
interface:

```text
realization at k
-> successor realization step
-> realization at k+1
-> contrapositive gap persistence at the defect boundary
```

The point is not to add new arithmetic power.  It keeps the mechanism-facing
obligation positive, while the old negative `gap_descends` form remains only a
derived readout.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- One-step atom-projection defect descent from an explicit positive
successor-realization step.

The source demand is lowered directly.  The atom gap is lowered only by taking
the contrapositive of the supplied forward step
`realization at k -> realization at k+1`. -/
theorem atom_projection_defect_descend_of_successor_realization_step
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (successor :
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) ->
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k + 1)) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact ⟨{
    demand := lowerDemandOfSourceStep source defect.demand
    noAtomRealization :=
      atom_pair_gap_persistence_of_successor_realization
        successor defect.noAtomRealization
  }⟩

/-- Repair-lift version of the successor-realization step.

This keeps `AtomProjectionDefectRepairLift` on the positive side: it first
reads a successor realization from the repair lift, then uses the generic
contrapositive theorem above. -/
theorem atom_projection_defect_descend_of_repair_lift_via_successor_realization_step
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (L :
      AtomProjectionDefectRepairLift
        Atomic SourceEvidence Residual n) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  atom_projection_defect_descend_of_successor_realization_step
    L.source_descent
    (atom_pair_successor_realization_of_repair_lift
      (L.realization_successor k))

/-- Bounded pair transport version, routed through the positive realization
step before contraposition. -/
theorem atom_projection_defect_descend_of_bounded_pair_transport_via_successor_realization_step
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound k : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (hk : k < bound) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  atom_projection_defect_descend_of_successor_realization_step
    source
    (bounded_realization_transport_lift_of_pair_transport
      pair_transport hk)

/-- Traced feasible defect descent from an explicit positive
successor-realization step.

This is the traced analogue of
`atom_projection_defect_descend_of_successor_realization_step`: source path and
trace data descend on the representation side, while arithmetic gap persistence
is just the contrapositive of the positive successor-realization step. -/
theorem traced_feasible_atom_projection_defect_descend_of_successor_realization_step
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (successor :
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) ->
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k + 1)) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact ⟨{
    demand :=
      lowerTracedFeasibleDemandOfSourceStep
        source step_path trace_descent defect.demand
    noAtomRealization :=
      atom_pair_gap_persistence_of_successor_realization
        successor defect.noAtomRealization
  }⟩

/-- Traced repair-lift version routed through the positive successor
realization step. -/
theorem traced_feasible_atom_projection_defect_descend_of_repair_lift_via_successor_realization_step
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (L :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  traced_feasible_atom_projection_defect_descend_of_successor_realization_step
    L.source_descent L.step_path L.trace_descent
    (atom_pair_successor_realization_of_repair_lift
      (L.realization_successor k))

/-- Traced bounded pair transport version, routed through the positive
realization step before contraposition. -/
theorem traced_feasible_atom_projection_defect_descend_of_bounded_pair_transport_via_successor_realization_step
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n bound k : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (hk : k < bound) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  traced_feasible_atom_projection_defect_descend_of_successor_realization_step
    source step_path trace_descent
    (bounded_realization_transport_lift_of_pair_transport
      pair_transport hk)


end RepresentationArithmeticAtomProjectionDefect
