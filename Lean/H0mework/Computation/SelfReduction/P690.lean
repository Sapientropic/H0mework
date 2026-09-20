import H0mework.Realization.Descent.P285
import H0mework.Computation.SelfReduction.P689

/-!
# Proposition 690: good-cover primitive descent produces a CNF witness

The intended phase-transition SAT route is not "flip bits in `{0,1}^n`".
It is:

1. produce a continuous primitive on `[0,1]^n` or a local chart;
2. locate clause obstructions as local H¹/overlap failures;
3. repair them chartwise using the P284/P285 local Poincare primitive bridge;
4. descend the locally repaired continuous/sign data to one discrete Boolean
   assignment.

This file formalizes the last certified step.  Given a convex good-cover
primitive producer, a chart assignment for every local clause, and overlap
consistency of those chart assignments, Lean proves that the descended Boolean
assignment verifies the CNF formula at the root.  It then packages that
assignment as the exact P689 kernel/sign producer.

Boundary: this is a certificate theorem, not a universal SAT algorithm.  It
does not prove that SVD always supplies the primitive, that every obstruction
chart can be repaired, that overlaps always glue, or that the process is
polynomial for all ratios.  Those are now explicit producer obligations.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

open AffineRelaxation.GeometryConnection

universe u v w

/-! ## CNF formula evaluation from local clause checks -/

/-- THEOREM 1: if every clause in a CNF formula evaluates to true, then the
whole formula evaluates to true. -/
theorem cnfFormula_eval_true_of_forall_clause {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool)
    (h : ∀ clause : CNFClause n, clause ∈ formula ->
      CNFClause.eval clause assignment = true) :
    CNFFormula.eval formula assignment = true := by
  induction formula with
  | nil =>
      simp [CNFFormula.eval]
  | cons clause rest ih =>
      have hhead : CNFClause.eval clause assignment = true := by
        exact h clause (by simp)
      have htail : CNFFormula.eval rest assignment = true := by
        exact ih (by
          intro c hc
          have hmem : c ∈ clause :: rest := by
            simp [hc]
          exact h c hmem)
      simpa [CNFFormula.eval, hhead] using htail

/-! ## Good-cover primitive descent certificate -/

variable {Index E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [Inhabited Index]

/-- A good-cover primitive descent certificate for one finite CNF formula.

`continuousPrimitive` names the continuous SVD/phase-space primitive candidate.
The proof does not inspect its coordinates; that relation belongs to the
producer side.  What Lean checks here is the certified descent:

* every clause is assigned to a chart;
* the local chart assignment satisfies that clause;
* chart assignments agree on overlaps strongly enough to descend to one global
  Boolean assignment.
-/
structure CNFGoodCoverPrimitiveDescent {n : Nat}
    (formula : CNFFormula n)
    (Index E F : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited Index] where
  goodCover :
    ConvexClosedOneFormGoodCoverData Index E F
  continuousPrimitive : E
  localAssignment : Index -> Nat -> Bool
  clauseChart : CNFClause n -> Index
  local_clause_verified :
    ∀ clause : CNFClause n, clause ∈ formula ->
      CNFClause.eval clause (localAssignment (clauseChart clause)) = true
  descentAssignment : Nat -> Bool
  overlap_consistent :
    ∀ i : Index, localAssignment i = descentAssignment

namespace CNFGoodCoverPrimitiveDescent

variable {n : Nat} {formula : CNFFormula n}
variable (D : CNFGoodCoverPrimitiveDescent formula Index E F)

/-- THEOREM 2: P285 supplies the local exact/no-H¹ Čech bridge on the good
cover carried by the descent certificate. -/
theorem goodCoverBridge :
    ConvexClosedOneFormGoodCoverData.GoodCoverCechDeRhamBridgeCertificate
      D.goodCover :=
  D.goodCover.goodCover_cechDeRham_bridge

/-- THEOREM 3: after overlap-consistent descent, every clause is true under the
global discrete assignment. -/
theorem global_clause_verified
    (clause : CNFClause n) (hmem : clause ∈ formula) :
    CNFClause.eval clause D.descentAssignment = true := by
  have hlocal := D.local_clause_verified clause hmem
  have hdesc : D.localAssignment (D.clauseChart clause) =
      D.descentAssignment :=
    D.overlap_consistent (D.clauseChart clause)
  rw [← hdesc]
  exact hlocal

/-- THEOREM 4: the descended assignment satisfies the whole CNF formula. -/
theorem formula_verified :
    CNFFormula.eval formula D.descentAssignment = true :=
  cnfFormula_eval_true_of_forall_clause
    formula D.descentAssignment D.global_clause_verified

/-- THEOREM 5: the descended assignment verifies the CNF root node. -/
theorem root_verified :
    CNFSATVerify formula (CNFSATNode.root n) D.descentAssignment := by
  constructor
  · exact D.formula_verified
  · intro i hi
    simp [CNFSATNode.root] at hi

/-- THEOREM 6: good-cover primitive descent implies ordinary CNF
satisfiability. -/
theorem satisfiable
    (D : CNFGoodCoverPrimitiveDescent formula Index E F) :
    CNFSatisfiable formula :=
  (cnfRoot_hasWitness_iff_satisfiable formula).1
    ⟨D.descentAssignment, D.root_verified⟩

/-- THEOREM 7: a successful good-cover descent is an exact zero-residual kernel
sign candidate. -/
def toKernelSignCandidate :
    CNFKernelSignCandidate formula where
  assignment := D.descentAssignment
  phaseResidual := 0
  residual_zero_iff_verified := by
    constructor
    · intro _hzero
      exact D.root_verified
    · intro _hverified
      rfl

/-- THEOREM 8: a successful good-cover descent is an exact P689 kernel/sign
producer. -/
def toExactKernelSignProducer :
    ExactCNFKernelSignProducer formula where
  candidate := D.toKernelSignCandidate
  residual_zero_iff_satisfiable := by
    constructor
    · intro _hzero
      exact D.satisfiable
    · intro _hsat
      rfl

/-- THEOREM 9: the good-cover descent producer emits a verified assignment iff
the CNF formula is satisfiable. -/
theorem producedVerifiedWitness_iff_satisfiable :
    WitnessProducerProjection.ProducedVerifiedWitness
        D.toExactKernelSignProducer.toRootWitnessProducerProjection () ↔
      CNFSatisfiable formula :=
  ExactCNFKernelSignProducer.producedVerifiedWitness_iff_satisfiable
    D.toExactKernelSignProducer

end CNFGoodCoverPrimitiveDescent

/-! ## Packaged certificate -/

/-- P690 certificate: local Poincare/good-cover primitive descent is a
root-level SAT witness producer once local clause repairs and overlap descent
are supplied. -/
structure GoodCoverPrimitiveDescentSATCertificate where
  p689_exact_kernel_root :
    ExactKernelSignSATBridgeCertificate
  to_exact_kernel_producer :
    ∀ {n : Nat} {formula : CNFFormula n}
      {Index E F : Type u}
      [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      [Inhabited Index]
      (_ : CNFGoodCoverPrimitiveDescent formula Index E F),
      ExactCNFKernelSignProducer formula
  root_producer_iff_satisfiable :
    ∀ {n : Nat} {formula : CNFFormula n}
      {Index E F : Type u}
      [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      [Inhabited Index]
      (D : CNFGoodCoverPrimitiveDescent formula Index E F),
      WitnessProducerProjection.ProducedVerifiedWitness
          D.toExactKernelSignProducer.toRootWitnessProducerProjection () ↔
        CNFSatisfiable formula

/-- DEFINITION 1: canonical P690 good-cover primitive descent SAT certificate.
-/
def goodCoverPrimitiveDescentSATCertificate :
    GoodCoverPrimitiveDescentSATCertificate where
  p689_exact_kernel_root := exactKernelSignSATBridgeCertificate
  to_exact_kernel_producer := by
    intro n formula Index E F _ _ _ _ _ _ D
    exact D.toExactKernelSignProducer
  root_producer_iff_satisfiable := by
    intro n formula Index E F _ _ _ _ _ _ D
    exact CNFGoodCoverPrimitiveDescent.producedVerifiedWitness_iff_satisfiable D

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P690 grand root: the P284/P285 good-cover primitive descent route into the
P689 exact SAT producer bridge.

This is the formal version of the current algorithmic insight: SVD/phase data
may give a continuous primitive; P284/P285 repair local obstruction charts; if
those chart repairs glue, the resulting discrete witness is certified.
-/
structure GoodCoverPrimitiveDescentSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p689_root :
    ExactKernelSignSATBridgeUnifiedRootCertificate.{u, v, w, z} E0
  good_cover_descent :
    GoodCoverPrimitiveDescentSATCertificate.{v}

/-- THEOREM 10: the good-cover primitive descent SAT unified root is inhabited.
-/
def goodCoverPrimitiveDescentSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    GoodCoverPrimitiveDescentSATUnifiedRootCertificate.{u, v, w, z} E0 where
  p689_root := exactKernelSignSATBridgeUnifiedRootCertificate (E := E0)
  good_cover_descent := goodCoverPrimitiveDescentSATCertificate

end GrandUnification

end SaturationMonoid
