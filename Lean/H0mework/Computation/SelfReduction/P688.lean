import H0mework.Computation.SelfReduction.P687

/-!
# Proposition 688: clean CNF phase implies SAT witness production

P687 instantiated the ordinary binary self-reduction for finite CNF/SAT under a
correct partial-node decision oracle.  P686 isolated the stronger carrier-phase
route: a clean/no-metastable consolidation phase with a sound and complete
freeze map is already a witness producer.

This file welds those two faces on the concrete CNF surface.  A clean phase
producer whose verifier is `CNFSATVerify formula` yields, at the CNF root, a
produced verified assignment iff the formula is satisfiable.  It also yields the
P157 active-memory-to-stored-memory transition and stored recall potential.

Boundary: this is still not `P = NP`.  The clean phase producer is supplied as
structure.  A genuine algorithmic theorem must still construct it from a clause
conflict topology, prove clean convergence/no metastability there, and attach a
polynomial cost bound.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

universe u

set_option linter.checkUnivs false

/-! ## CNF-specialized clean phase producer -/

/-- A clean consolidation phase producer specialized to a finite CNF formula.

`Stored` is deliberately abstract: a future clause-conflict carrier theorem has
to instantiate it and prove the clean/no-metastable fields.  The only fixed
surface here is the verifier: it must be exactly `CNFSATVerify formula`.
-/
structure CNFCleanConsolidationPhaseProducer {n : Nat}
    (formula : CNFFormula n) (Stored : Type u) where
  phase :
    CleanConsolidationPhaseProducer
      (CNFSATNode n) Stored (Nat -> Bool)
  verify_eq : phase.verify = CNFSATVerify formula

namespace CNFCleanConsolidationPhaseProducer

variable {n : Nat} {Stored : Type u}
variable {formula : CNFFormula n}
variable (C : CNFCleanConsolidationPhaseProducer formula Stored)

/-- THEOREM 1: a CNF clean phase producer compiles to P684's witness producer
projection on the concrete partial-assignment node surface. -/
def toWitnessProducerProjection :
    WitnessProducerProjection (CNFSATNode n) (Nat -> Bool) :=
  C.phase.toWitnessProducerProjection

/-- THEOREM 2: on any partial CNF node, the clean phase producer emits a
verified witness iff a verifier witness exists. -/
theorem producedVerifiedWitness_iff_hasWitness (x : CNFSATNode n) :
    C.toWitnessProducerProjection.ProducedVerifiedWitness x ↔
      C.toWitnessProducerProjection.HasWitness x :=
  C.phase.producedVerifiedWitness_iff_hasWitness x

/-- THEOREM 3: at the root, clean CNF phase production is equivalent to
ordinary CNF satisfiability. -/
theorem rootProducedVerifiedWitness_iff_satisfiable :
    C.toWitnessProducerProjection.ProducedVerifiedWitness
        (CNFSATNode.root n) ↔
      CNFSatisfiable formula := by
  rw [C.producedVerifiedWitness_iff_hasWitness]
  change (∃ assignment : Nat -> Bool,
      C.phase.verify (CNFSATNode.root n) assignment) ↔
    CNFSatisfiable formula
  rw [C.verify_eq]
  exact cnfRoot_hasWitness_iff_satisfiable formula

/-- THEOREM 4: if the CNF is satisfiable, the clean phase gives the P157
active-memory-to-stored-memory transition at the root. -/
theorem rootConsolidationPhaseTransition_of_satisfiable
    (h : CNFSatisfiable formula) :
    ∃ T : ConsolidationPhaseTransition
          C.phase.activeRecollectionAct C.phase.storedWitnessData,
      T.activeState = CNFSATNode.root n /\
        T.longTermState = C.phase.consolidate (CNFSATNode.root n) := by
  have hw0 :
      ∃ assignment : Nat -> Bool,
        CNFSATVerify formula (CNFSATNode.root n) assignment :=
    (cnfRoot_hasWitness_iff_satisfiable formula).2 h
  have hw :
      ∃ assignment : Nat -> Bool,
        C.phase.verify (CNFSATNode.root n) assignment := by
    simpa [C.verify_eq] using hw0
  exact C.phase.consolidationPhaseTransition_of_hasWitness
    (CNFSATNode.root n) hw

/-- THEOREM 5: if the CNF is satisfiable, the stored normal form at the root
has store-backed recollectable potential. -/
theorem rootStoredRecallPotential_of_satisfiable
    (h : CNFSatisfiable formula) :
    RecollectableMemoryPotential
      (storageRecallAct C.phase.storedWitnessData)
      (C.phase.consolidate (CNFSATNode.root n)) := by
  have hw0 :
      ∃ assignment : Nat -> Bool,
        CNFSATVerify formula (CNFSATNode.root n) assignment :=
    (cnfRoot_hasWitness_iff_satisfiable formula).2 h
  have hw :
      ∃ assignment : Nat -> Bool,
        C.phase.verify (CNFSATNode.root n) assignment := by
    simpa [C.verify_eq] using hw0
  exact C.phase.storedRecallPotential_of_hasWitness
    (CNFSATNode.root n) hw

end CNFCleanConsolidationPhaseProducer

/-! ## Packaged certificate -/

/-- P688 certificate: clean/no-metastable consolidation, when specialized to
the CNF verifier, yields root-level SAT witness production plus the P157
active-to-stored transition. -/
structure CNFCleanPhaseSATProducerCertificate where
  p687_self_reduction_root :
    CNFSATSelfReductionCertificate
  to_witness_projection :
    ∀ {n : Nat} {Stored : Type u} {formula : CNFFormula n}
      (_ : CNFCleanConsolidationPhaseProducer formula Stored),
      WitnessProducerProjection (CNFSATNode n) (Nat -> Bool)
  root_producer_iff_satisfiable :
    ∀ {n : Nat} {Stored : Type u} {formula : CNFFormula n}
      (C : CNFCleanConsolidationPhaseProducer formula Stored),
      C.toWitnessProducerProjection.ProducedVerifiedWitness
          (CNFSATNode.root n) ↔
        CNFSatisfiable formula
  root_transition_of_satisfiable :
    ∀ {n : Nat} {Stored : Type u} {formula : CNFFormula n}
      (C : CNFCleanConsolidationPhaseProducer formula Stored),
      CNFSatisfiable formula ->
        ∃ T : ConsolidationPhaseTransition
              C.phase.activeRecollectionAct C.phase.storedWitnessData,
          T.activeState = CNFSATNode.root n /\
            T.longTermState = C.phase.consolidate (CNFSATNode.root n)
  root_stored_recall_of_satisfiable :
    ∀ {n : Nat} {Stored : Type u} {formula : CNFFormula n}
      (C : CNFCleanConsolidationPhaseProducer formula Stored),
      CNFSatisfiable formula ->
        RecollectableMemoryPotential
          (storageRecallAct C.phase.storedWitnessData)
          (C.phase.consolidate (CNFSATNode.root n))

/-- DEFINITION 1: canonical P688 CNF clean-phase producer certificate. -/
def cnfCleanPhaseSATProducerCertificate :
    CNFCleanPhaseSATProducerCertificate.{u} where
  p687_self_reduction_root := cnfSATSelfReductionCertificate
  to_witness_projection := by
    intro n Stored formula C
    exact C.toWitnessProducerProjection
  root_producer_iff_satisfiable := by
    intro n Stored formula C
    exact C.rootProducedVerifiedWitness_iff_satisfiable
  root_transition_of_satisfiable := by
    intro n Stored formula C h
    exact C.rootConsolidationPhaseTransition_of_satisfiable h
  root_stored_recall_of_satisfiable := by
    intro n Stored formula C h
    exact C.rootStoredRecallPotential_of_satisfiable h

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P688 grand root: the finite CNF self-reduction surface plus the clean CNF
phase bridge to SAT witness production and P157 consolidation.

This is the exact formal slot for the user's "clean phase at `σ = 1/2`
freezes to a discrete witness at `σ = 0`" claim.  The construction of such a
clean phase for real clause-conflict dynamics remains the producer debt.
-/
structure CNFCleanPhaseSATUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p687_root :
    CNFSATSelfReductionUnifiedRootCertificate.{u, v, w, z} E
  clean_cnf_phase :
    CNFCleanPhaseSATProducerCertificate.{v}

/-- THEOREM 6: the CNF clean-phase SAT unified root is inhabited. -/
def cnfCleanPhaseSATUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CNFCleanPhaseSATUnifiedRootCertificate.{u, v, w, z} E where
  p687_root := cnfSATSelfReductionUnifiedRootCertificate (E := E)
  clean_cnf_phase := cnfCleanPhaseSATProducerCertificate

end GrandUnification

end SaturationMonoid
