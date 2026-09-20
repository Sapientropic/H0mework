/-
  Proposition 119: finite reflexive interaction rings generate their own
  finite-cycle phase cochains.

  Proposition 114 proves the finite-cycle H¹ theorem for a supplied phase
  cochain.  Proposition 118 proves the three-agent generated case.  This file
  removes the remaining mismatch: for any finite reflexive interaction ring,
  the selected edge phase is forced by the read/write structure itself:

      downstream.read (upstream.write upstream.base)
        - downstream.read downstream.base

  Thus a noncancelled generated residual is not a runtime-supplied phase map.
  It is the additive observation difference around the reflexive interaction
  ring.  Runtime still owes mechanism-faithfulness: that a concrete system
  instantiates the ring and that the selected additive observation layer is the
  layer the product treats as visible.
-/

import H0mework.Realization.CyclicMemory.P114

/-! ## Finite generated interaction rings -/

/-- A finite reflexive interaction ring.  `next` is the trigger permutation:
agent `i`'s write is read by agent `next i`. -/
structure FiniteReflexiveInteractionRing
    (Index State A : Type*) [Fintype Index] [AddCommGroup A] where
  next : Equiv.Perm Index
  query : Index -> ReflexiveQuery State A
  base : Index -> State
  nondegenerate : 3 <= Fintype.card Index

namespace FiniteReflexiveInteractionRing

variable {Index State A : Type*} [Fintype Index] [AddCommGroup A]

/-- The interaction phase forced by the read/write loops. -/
def generatedInteractionPhase
    (R : FiniteReflexiveInteractionRing Index State A) :
    Index -> Index -> A :=
  fun i j =>
    (R.query j).read ((R.query i).write (R.base i)) -
      (R.query j).read (R.base j)

/-- The accumulated generated residual on the selected trigger ring. -/
def generatedResidual
    (R : FiniteReflexiveInteractionRing Index State A) : A :=
  ∑ i, R.generatedInteractionPhase i (R.next i)

/-- The generated residual is noncancelled exactly when the generated phase has
nonzero selected-cycle residual. -/
def GeneratedNoncancelled
    (R : FiniteReflexiveInteractionRing Index State A) : Prop :=
  NoncancelledCycleResidual R.next R.generatedInteractionPhase

/-- A selected edge changed a downstream read when the downstream agent observes
a different additive value after the upstream write. -/
def EdgeReadChanged
    (R : FiniteReflexiveInteractionRing Index State A)
    (i : Index) : Prop :=
  (R.query (R.next i)).read ((R.query i).write (R.base i)) ≠
    (R.query (R.next i)).read (R.base (R.next i))

/-- THEOREM 1: on each selected edge, generated phase nonzero is exactly changed
downstream read in the chosen additive observation layer. -/
theorem generatedInteractionPhase_edge_nonzero_iff_readChanged
    (R : FiniteReflexiveInteractionRing Index State A) (i : Index) :
    R.generatedInteractionPhase i (R.next i) ≠ 0 <-> R.EdgeReadChanged i := by
  simp [generatedInteractionPhase, EdgeReadChanged, sub_ne_zero]

/-- THEOREM 2: nonzero generated residual is the same as generated
noncancellation. -/
theorem generatedResidual_nonzero_iff_noncancelled
    (R : FiniteReflexiveInteractionRing Index State A) :
    R.generatedResidual ≠ 0 <-> R.GeneratedNoncancelled := by
  rfl

/-! ## Noncancelled generated residual forces changed reads -/

/-- THEOREM 3: a noncancelled finite residual has at least one nonzero selected
edge phase. -/
theorem finiteResidual_nonzero_exists_edge_nonzero
    {next : Equiv.Perm Index} {c : Index -> Index -> A}
    (hres : NoncancelledCycleResidual next c) :
    exists i, c i (next i) ≠ 0 := by
  by_contra hnone
  have hedgeZero : forall i, c i (next i) = 0 := by
    intro i
    by_contra hne
    exact hnone ⟨i, hne⟩
  have hsum : (∑ i, c i (next i)) = 0 := by
    simp [hedgeZero]
  exact hres hsum

/-- THEOREM 4: a nonzero generated residual implies at least one downstream
read changed. -/
theorem generatedResidual_nonzero_exists_readChanged
    (R : FiniteReflexiveInteractionRing Index State A)
    (hres : R.generatedResidual ≠ 0) :
    exists i, R.EdgeReadChanged i := by
  have hnc : R.GeneratedNoncancelled := by
    exact (R.generatedResidual_nonzero_iff_noncancelled).mp hres
  rcases finiteResidual_nonzero_exists_edge_nonzero hnc with ⟨i, hi⟩
  exact ⟨i, (R.generatedInteractionPhase_edge_nonzero_iff_readChanged i).mp hi⟩

/-! ## Generated rings instantiate the finite-cycle H¹ certificate -/

/-- A finite reflexive interaction ring with noncancelled generated residual is
exactly a P114 finite cyclic interaction certificate. -/
def toFiniteCyclicInteractionCertificate
    (R : FiniteReflexiveInteractionRing Index State A)
    (hnc : R.GeneratedNoncancelled) :
    FiniteCyclicInteractionCertificate Index A where
  next := R.next
  phase := R.generatedInteractionPhase
  nondegenerate := R.nondegenerate
  noncancelled := hnc

/-- THEOREM 5: nonzero generated residual gives a genuine H¹ obstruction for
the generated phase cochain. -/
theorem generatedResidual_nonzero_h1
    (R : FiniteReflexiveInteractionRing Index State A)
    (hres : R.generatedResidual ≠ 0) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index A)
      R.generatedInteractionPhase := by
  have hnc : R.GeneratedNoncancelled := by
    exact (R.generatedResidual_nonzero_iff_noncancelled).mp hres
  exact (R.toFiniteCyclicInteractionCertificate hnc).h1Obstruction

/-- THEOREM 6: the same residual rules out global-potential explanation on the
selected cycle edges. -/
theorem generatedResidual_nonzero_no_global_cycle_potential
    (R : FiniteReflexiveInteractionRing Index State A)
    (hres : R.generatedResidual ≠ 0) :
    Not (CycleEdgePotentialExplained R.next R.generatedInteractionPhase) := by
  have hnc : R.GeneratedNoncancelled := by
    exact (R.generatedResidual_nonzero_iff_noncancelled).mp hres
  exact (R.toFiniteCyclicInteractionCertificate hnc).not_cycleEdgePotentialExplained

/-- THEOREM 7: nonzero generated residual simultaneously gives H¹ and a
changed-read witness. -/
theorem generatedResidual_nonzero_h1_and_readChanged
    (R : FiniteReflexiveInteractionRing Index State A)
    (hres : R.generatedResidual ≠ 0) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index A)
        R.generatedInteractionPhase /\
      exists i, R.EdgeReadChanged i := by
  exact ⟨R.generatedResidual_nonzero_h1 hres,
    R.generatedResidual_nonzero_exists_readChanged hres⟩

/-! ## Integer magnitude -/

/-- Computable residual magnitude for integer-valued finite generated rings. -/
def generatedResidualMagnitude
    {Index State : Type*} [Fintype Index]
    (R : FiniteReflexiveInteractionRing Index State Int) : Nat :=
  Int.natAbs R.generatedResidual

/-- THEOREM 8: positive generated magnitude gives H¹ and a changed-read witness
for any finite generated integer-valued ring. -/
theorem generatedResidualMagnitude_pos_h1_and_readChanged
    {Index State : Type*} [Fintype Index]
    (R : FiniteReflexiveInteractionRing Index State Int)
    (hpos : 0 < R.generatedResidualMagnitude) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index Int)
        R.generatedInteractionPhase /\
      exists i, R.EdgeReadChanged i := by
  have hres : R.generatedResidual ≠ 0 := by
    exact (Int.natAbs_pos).mp hpos
  exact R.generatedResidual_nonzero_h1_and_readChanged hres

end FiniteReflexiveInteractionRing

/-!
  Summary:
  - Finite reflexive read/write interaction rings generate their own phase
    cochains; the phase map is not an empirical add-on.
  - Noncancelled generated residual gives H¹, rules out global-potential
    explanation on the selected edges, and forces at least one downstream read
    change in the chosen additive observation layer.
  - The remaining production boundary is not "emit some phase cochain"; it is
    narrower: instantiate this finite ring and justify the observation layer.
-/
