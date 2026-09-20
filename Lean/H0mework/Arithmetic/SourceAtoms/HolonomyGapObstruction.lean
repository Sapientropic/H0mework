import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Holonomy gap obstruction

This file records an abstract holonomy-style obstruction for stable projection
gaps.  It is not a Goldbach producer and it does not construct atom pairs.

The useful shape is:

```text
projection defect
-> closed source holonomy loop
-> strict residual-energy drop along that closed loop
-> contradiction
```

The hard future theorem is to derive such a closed strict residual holonomy
from representation / GT / crystal / branching dynamics.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- A closed holonomy loop with strict residual-energy drop.

The contradiction is deliberately elementary: a loop cannot return to the same
source evidence while making a Nat-valued residual strictly smaller.  The
structure is useful as a target for future source-side dynamics. -/
structure ClosedStrictResidualHolonomy
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence) where
  source : SourceEvidence
  target : SourceEvidence
  closes : target = source
  residual_drops :
    Residual.residualEnergy target < Residual.residualEnergy source

/-- Closed strict residual holonomy is impossible. -/
theorem no_closed_strict_residual_holonomy
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence} :
    ¬ Nonempty (ClosedStrictResidualHolonomy SourceEvidence Residual) := by
  intro h
  rcases h with ⟨H⟩
  have hDrop := H.residual_drops
  rw [H.closes] at hDrop
  exact Nat.lt_irrefl (Residual.residualEnergy H.source) hDrop

/-- A feasible atom-projection defect holonomy obstruction law.

This is the source-side socket for the holonomy candidate: every feasible
projection defect must induce a closed residual holonomy loop that strictly
drops residual energy.  Such a law is extremely strong and must be earned from
real representation dynamics; it is not supplied by endpoint coverage. -/
structure FeasibleAtomProjectionDefectHolonomyObstructionLaw
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  terminalEvidence :
    ∀ {k : Nat},
      FeasibleAtomProjectionDefect
        Atomic SourceEvidence Residual Source n k ->
        SourceEvidence
  closes :
    ∀ {k : Nat}
      (defect :
        FeasibleAtomProjectionDefect
          Atomic SourceEvidence Residual Source n k),
        terminalEvidence defect = defect.demand.demand.evidence
  residual_drops :
    ∀ {k : Nat}
      (defect :
        FeasibleAtomProjectionDefect
          Atomic SourceEvidence Residual Source n k),
        Residual.residualEnergy (terminalEvidence defect) <
          Residual.residualEnergy defect.demand.demand.evidence

/-- A feasible defect holonomy obstruction law excludes all feasible
atom-projection defects in the fiber. -/
theorem no_feasible_atom_projection_defect_of_holonomy_obstruction
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (L :
      FeasibleAtomProjectionDefectHolonomyObstructionLaw
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (FeasibleAtomProjectionDefect
          Atomic SourceEvidence Residual Source n k) := by
  intro k hDefect
  rcases hDefect with ⟨defect⟩
  have hDrop := L.residual_drops defect
  rw [L.closes defect] at hDrop
  exact
    Nat.lt_irrefl
      (Residual.residualEnergy defect.demand.demand.evidence)
      hDrop

/-- Demand-level consequence of feasible holonomy obstruction.

As with finite descent, the theorem returns `not not exists atom pair`; it does
not extract an endpoint witness. -/
theorem not_not_atom_realization_of_feasible_demand_by_holonomy_obstruction
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (L :
      FeasibleAtomProjectionDefectHolonomyObstructionLaw
        Atomic SourceEvidence Residual Source n)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  intro hMissing
  exact
    (no_feasible_atom_projection_defect_of_holonomy_obstruction L k)
      ⟨{ demand := demand, noAtomRealization := hMissing }⟩

/-- Traced feasible version of the holonomy obstruction law.

The traced version keeps sourcePath / phaseTrace / sigmaTag / producerTrace in
the defect object, so future source-side proofs cannot silently drop the
active repair trace before invoking holonomy. -/
structure TracedFeasibleAtomProjectionDefectHolonomyObstructionLaw
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  terminalEvidence :
    ∀ {k : Nat},
      TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k ->
        SourceEvidence
  closes :
    ∀ {k : Nat}
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k),
        terminalEvidence defect =
          defect.demand.demand.demand.evidence
  residual_drops :
    ∀ {k : Nat}
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k),
        Residual.residualEnergy (terminalEvidence defect) <
          Residual.residualEnergy defect.demand.demand.demand.evidence

/-- A traced feasible holonomy obstruction law excludes all traced feasible
atom-projection defects in the fiber. -/
theorem no_traced_feasible_atom_projection_defect_of_holonomy_obstruction
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (L :
      TracedFeasibleAtomProjectionDefectHolonomyObstructionLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) := by
  intro k hDefect
  rcases hDefect with ⟨defect⟩
  have hDrop := L.residual_drops defect
  rw [L.closes defect] at hDrop
  exact
    Nat.lt_irrefl
      (Residual.residualEnergy defect.demand.demand.demand.evidence)
      hDrop

/-- Demand-level consequence of traced feasible holonomy obstruction. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_holonomy_obstruction
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (L :
      TracedFeasibleAtomProjectionDefectHolonomyObstructionLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  intro hMissing
  exact
    (no_traced_feasible_atom_projection_defect_of_holonomy_obstruction L k)
      ⟨{ demand := demand, noAtomRealization := hMissing }⟩


end RepresentationArithmeticAtomProjectionDefect
