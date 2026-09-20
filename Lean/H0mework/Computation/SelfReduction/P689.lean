import H0mework.Computation.SelfReduction.P688

/-!
# Proposition 689: SVD/H1 kernel sign candidates as SAT producer certificates

The experimental bridge says: the sign pattern of a smallest-obstruction
kernel direction often satisfies a SAT instance outright, especially below the
observed clause/variable-ratio transition.  This file records the exact
machine-checkable theorem that such an experiment has to feed Lean.

It does **not** prove that SVD solves SAT, that ratio `≤ 3` always succeeds, or
that the runtime is polynomial for all SAT.  It proves the bridge shape:

* a kernel/sign candidate carries an assignment and a phase residual;
* residual zero is the formal "H1 obstruction vanished" condition;
* if residual zero is equivalent to CNF satisfiability, the candidate is a
  sound-and-complete P684 witness producer at the root;
* a nonzero residual is therefore not hidden failure, but the exact obstruction
  gap that the notes report as `29/30`, `best = ...`, or phase-transition
  failure.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

/-! ## Kernel sign candidates -/

/-- A root-level SVD/H1 kernel sign candidate for a CNF formula.

`assignment` is the Boolean sign pattern extracted from the kernel direction.
`phaseResidual` is an abstract natural-valued obstruction count/defect.  In a
runtime harness this can be "unsatisfied clauses", "residual clauses", or any
certified nonnegative obstruction measure.  Lean only needs the zero test to be
faithful to `CNFSATVerify`.
-/
structure CNFKernelSignCandidate {n : Nat} (formula : CNFFormula n) where
  assignment : Nat -> Bool
  phaseResidual : Nat
  residual_zero_iff_verified :
    phaseResidual = 0 ↔
      CNFSATVerify formula (CNFSATNode.root n) assignment

namespace CNFKernelSignCandidate

variable {n : Nat} {formula : CNFFormula n}
variable (K : CNFKernelSignCandidate formula)

/-- THEOREM 1: residual zero means the kernel sign candidate is an actual SAT
witness. -/
theorem verified_of_residual_zero (h : K.phaseResidual = 0) :
    CNFSATVerify formula (CNFSATNode.root n) K.assignment :=
  K.residual_zero_iff_verified.1 h

/-- THEOREM 2: residual zero implies ordinary satisfiability. -/
theorem satisfiable_of_residual_zero (h : K.phaseResidual = 0) :
    CNFSatisfiable formula :=
  (cnfRoot_hasWitness_iff_satisfiable formula).1
    ⟨K.assignment, K.verified_of_residual_zero h⟩

/-- THEOREM 3: if the candidate is verified, the phase residual vanishes. -/
theorem residual_zero_of_verified
    (h : CNFSATVerify formula (CNFSATNode.root n) K.assignment) :
    K.phaseResidual = 0 :=
  K.residual_zero_iff_verified.2 h

end CNFKernelSignCandidate

/-! ## Exact SVD/kernel producer certificates -/

/-- An exact root-level kernel producer certificate.

The additional field is the whole hard bridge: residual zero is equivalent to
the formula being satisfiable.  Empirical SVD evidence can motivate this field
on a family, but Lean treats it as the proof obligation that separates a
working producer from a near miss.
-/
structure ExactCNFKernelSignProducer {n : Nat} (formula : CNFFormula n) where
  candidate : CNFKernelSignCandidate formula
  residual_zero_iff_satisfiable :
    candidate.phaseResidual = 0 ↔ CNFSatisfiable formula

namespace ExactCNFKernelSignProducer

variable {n : Nat} {formula : CNFFormula n}
variable (K : ExactCNFKernelSignProducer formula)

/-- The candidate producer: emit the kernel sign assignment exactly when the
certified phase residual vanishes. -/
def rootProducer : Option (Nat -> Bool) :=
  if K.candidate.phaseResidual = 0 then
    some K.candidate.assignment
  else
    none

/-- THEOREM 4: the kernel producer is sound at the CNF root. -/
theorem rootProducer_sound {assignment : Nat -> Bool}
    (h : K.rootProducer = some assignment) :
    CNFSATVerify formula (CNFSATNode.root n) assignment := by
  by_cases hz : K.candidate.phaseResidual = 0
  · have hsome : some K.candidate.assignment = some assignment := by
      simpa [rootProducer, hz] using h
    have heq : K.candidate.assignment = assignment := by
      simpa using Option.some.inj hsome
    rw [← heq]
    exact K.candidate.verified_of_residual_zero hz
  · have : False := by
      simp [rootProducer, hz] at h
    exact False.elim this

/-- THEOREM 5: if the formula is satisfiable, the exact kernel producer emits
the certified sign assignment. -/
theorem rootProducer_complete
    (h : CNFSatisfiable formula) :
    ∃ assignment : Nat -> Bool, K.rootProducer = some assignment := by
  have hz : K.candidate.phaseResidual = 0 :=
    K.residual_zero_iff_satisfiable.2 h
  exact ⟨K.candidate.assignment, by simp [rootProducer, hz]⟩

/-- THEOREM 6: an exact kernel sign producer is a P684 root witness-producer
projection.  The instance type is `Unit` because this is a fixed-formula,
root-level certificate. -/
def toRootWitnessProducerProjection :
    WitnessProducerProjection Unit (Nat -> Bool) where
  verify := fun _ assignment =>
    CNFSATVerify formula (CNFSATNode.root n) assignment
  producer := fun _ => K.rootProducer
  sound := by
    intro _ assignment h
    exact K.rootProducer_sound h
  complete := by
    intro _ h
    have hs : CNFSatisfiable formula :=
      (cnfRoot_hasWitness_iff_satisfiable formula).1 h
    exact K.rootProducer_complete hs

/-- THEOREM 7: exact kernel sign production collapses root production and
ordinary satisfiability. -/
theorem producedVerifiedWitness_iff_satisfiable :
    K.toRootWitnessProducerProjection.ProducedVerifiedWitness () ↔
      CNFSatisfiable formula := by
  rw [K.toRootWitnessProducerProjection.producedVerifiedWitness_iff_hasWitness]
  exact cnfRoot_hasWitness_iff_satisfiable formula

/-- THEOREM 8: nonzero residual is exactly the obstruction to this particular
kernel candidate being an exact root producer. -/
theorem residual_ne_zero_iff_not_satisfiable :
    K.candidate.phaseResidual ≠ 0 ↔ ¬ CNFSatisfiable formula := by
  constructor
  · intro hnz hs
    exact hnz (K.residual_zero_iff_satisfiable.2 hs)
  · intro hunsat hz
    exact hunsat (K.residual_zero_iff_satisfiable.1 hz)

end ExactCNFKernelSignProducer

/-! ## Packaged certificate -/

/-- P689 certificate: the exact SVD/H1 kernel bridge is a producer theorem once
residual zero is certified equivalent to satisfiability. -/
structure ExactKernelSignSATBridgeCertificate where
  p688_clean_phase_root :
    CNFCleanPhaseSATProducerCertificate.{0}
  to_root_projection :
    ∀ {n : Nat} {formula : CNFFormula n}
      (_ : ExactCNFKernelSignProducer formula),
      WitnessProducerProjection Unit (Nat -> Bool)
  root_producer_iff_satisfiable :
    ∀ {n : Nat} {formula : CNFFormula n}
      (K : ExactCNFKernelSignProducer formula),
      K.toRootWitnessProducerProjection.ProducedVerifiedWitness () ↔
        CNFSatisfiable formula
  residual_obstruction_iff_unsat :
    ∀ {n : Nat} {formula : CNFFormula n}
      (K : ExactCNFKernelSignProducer formula),
      K.candidate.phaseResidual ≠ 0 ↔ ¬ CNFSatisfiable formula

/-- DEFINITION 1: canonical P689 exact kernel-sign bridge certificate. -/
def exactKernelSignSATBridgeCertificate :
    ExactKernelSignSATBridgeCertificate where
  p688_clean_phase_root := cnfCleanPhaseSATProducerCertificate
  to_root_projection := by
    intro n formula K
    exact K.toRootWitnessProducerProjection
  root_producer_iff_satisfiable := by
    intro n formula K
    exact K.producedVerifiedWitness_iff_satisfiable
  residual_obstruction_iff_unsat := by
    intro n formula K
    exact K.residual_ne_zero_iff_not_satisfiable

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P689 grand root: the exact kernel/sign bridge as a root SAT producer
certificate, layered over the P688 clean CNF phase root.

This is the formal shape of the SVD/H1 observation.  Runtime data can now be
classified cleanly: a zero residual instance supplies this certificate; a
nonzero residual is an obstruction gap, not a hidden proof.
-/
structure ExactKernelSignSATBridgeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p688_root :
    CNFCleanPhaseSATUnifiedRootCertificate.{u, v, w, z} E
  exact_kernel_sign_bridge :
    ExactKernelSignSATBridgeCertificate

/-- THEOREM 9: the exact kernel/sign SAT bridge unified root is inhabited. -/
def exactKernelSignSATBridgeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    ExactKernelSignSATBridgeUnifiedRootCertificate.{u, v, w, z} E where
  p688_root := cnfCleanPhaseSATUnifiedRootCertificate (E := E)
  exact_kernel_sign_bridge := exactKernelSignSATBridgeCertificate

end GrandUnification

end SaturationMonoid
