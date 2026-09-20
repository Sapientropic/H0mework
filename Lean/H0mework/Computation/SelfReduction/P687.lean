import H0mework.Computation.SelfReduction.P686

/-!
# Proposition 687: concrete finite CNF self-reduction

P685 proved that a correct binary self-reduction decision oracle yields a
witness producer.  P686 isolated the clean-consolidation route to such a
producer.  This file instantiates P685 with an actual finite CNF/SAT surface:

* variables are `Fin n`;
* a partial node fixes the first `depth` Boolean variables;
* `left`/`right` extend the prefix by assigning the next variable false/true;
* a correct SAT decider for partial nodes therefore yields a witness-producing
  SAT assignment search.

Boundary: this is still not `P = NP`.  The decider is an explicitly supplied
oracle with a correctness proof.  The theorem proves the classical
decision-to-witness self-reduction for finite CNF; polynomial time would still
require a polynomial-time implementation of that decider or a concrete clean
phase producer for the same CNF surface.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

set_option linter.checkUnivs false

/-! ## Finite CNF syntax -/

/-- A literal over `n` Boolean variables.  `positive = true` reads the variable;
`positive = false` reads its negation. -/
structure CNFLiteral (n : Nat) where
  var : Fin n
  positive : Bool
  deriving DecidableEq, Repr

namespace CNFLiteral

/-- Evaluate a literal under a total Boolean assignment. -/
def eval {n : Nat} (lit : CNFLiteral n) (assignment : Nat -> Bool) : Bool :=
  if lit.positive then assignment lit.var.val else !(assignment lit.var.val)

end CNFLiteral

abbrev CNFClause (n : Nat) := List (CNFLiteral n)
abbrev CNFFormula (n : Nat) := List (CNFClause n)

namespace CNFClause

/-- A clause is satisfied when at least one literal is true. -/
def eval {n : Nat} (clause : CNFClause n)
    (assignment : Nat -> Bool) : Bool :=
  clause.any (fun lit => lit.eval assignment)

end CNFClause

namespace CNFFormula

/-- A CNF formula is satisfied when every clause is true. -/
def eval {n : Nat} (formula : CNFFormula n)
    (assignment : Nat -> Bool) : Bool :=
  formula.all (fun clause => CNFClause.eval clause assignment)

end CNFFormula

/-! ## Partial-assignment nodes -/

/-- A SAT self-reduction node: the first `depth` variables have been assigned
by `pref`; variables at indices `>= depth` are still open. -/
structure CNFSATNode (n : Nat) where
  depth : Nat
  hdepth : depth ≤ n
  pref : Nat -> Bool

namespace CNFSATNode

/-- The root node has no assigned variables. -/
def root (n : Nat) : CNFSATNode n where
  depth := 0
  hdepth := Nat.zero_le n
  pref := fun _ => false

/-- Remaining unresolved variables. -/
def rank {n : Nat} (x : CNFSATNode n) : Nat :=
  n - x.depth

/-- Extend a node by assigning the next variable to `bit`; at terminal nodes,
extension is the identity. -/
def extend {n : Nat} (x : CNFSATNode n) (bit : Bool) : CNFSATNode n :=
  if h : x.depth < n then
    { depth := x.depth + 1
      hdepth := Nat.succ_le_of_lt h
      pref := fun i => if i = x.depth then bit else x.pref i }
  else
    x

def left {n : Nat} (x : CNFSATNode n) : CNFSATNode n :=
  x.extend false

def right {n : Nat} (x : CNFSATNode n) : CNFSATNode n :=
  x.extend true

end CNFSATNode

/-- A total assignment verifies a partial SAT node when it satisfies the CNF and
agrees with all assigned prefix variables. -/
def CNFSATVerify {n : Nat} (formula : CNFFormula n)
    (x : CNFSATNode n) (assignment : Nat -> Bool) : Prop :=
  CNFFormula.eval formula assignment = true /\
    ∀ i : Nat, i < x.depth -> assignment i = x.pref i

/-- Satisfiability at the root, with no prefix constraints. -/
def CNFSatisfiable {n : Nat} (formula : CNFFormula n) : Prop :=
  ∃ assignment : Nat -> Bool, CNFFormula.eval formula assignment = true

/-! ## Prefix-extension lemmas -/

/-- THEOREM 1: a witness for an extended node is a witness for the parent node.
-/
theorem cnfSATVerify_extend_sound {n : Nat} (formula : CNFFormula n)
    (x : CNFSATNode n) (bit : Bool) (assignment : Nat -> Bool) :
    CNFSATVerify formula (x.extend bit) assignment ->
      CNFSATVerify formula x assignment := by
  intro h
  by_cases hlt : x.depth < n
  · constructor
    · exact h.1
    · intro i hi
      have hi_ext : i < (x.extend bit).depth := by
        simp [CNFSATNode.extend, hlt]
        omega
      have hprefix := h.2 i hi_ext
      have hne : i ≠ x.depth := by
        omega
      simpa [CNFSATNode.extend, hlt, hne] using hprefix
  · simpa [CNFSATNode.extend, hlt] using h

/-- THEOREM 2: if a parent witness assigns the next variable to `bit`, it is a
witness for the corresponding extended child. -/
theorem cnfSATVerify_extend_complete {n : Nat} (formula : CNFFormula n)
    (x : CNFSATNode n) (bit : Bool) (assignment : Nat -> Bool)
    (hpos : 0 < x.rank)
    (hbit : assignment x.depth = bit)
    (h : CNFSATVerify formula x assignment) :
    CNFSATVerify formula (x.extend bit) assignment := by
  have hlt : x.depth < n := by
    simp [CNFSATNode.rank] at hpos
    omega
  constructor
  · exact h.1
  · intro i hi
    by_cases heq : i = x.depth
    · simpa [CNFSATNode.extend, hlt, heq] using hbit
    · have hi_old : i < x.depth := by
        have hi_ext : i < x.depth + 1 := by
          simpa [CNFSATNode.extend, hlt] using hi
        omega
      have hprefix := h.2 i hi_old
      simpa [CNFSATNode.extend, hlt, heq] using hprefix

/-- THEOREM 3: extending a positive-rank node strictly lowers the rank. -/
theorem cnfSATNode_rank_extend_lt {n : Nat}
    (x : CNFSATNode n) (bit : Bool) (hpos : 0 < x.rank) :
    (x.extend bit).rank < x.rank := by
  have hlt : x.depth < n := by
    simp [CNFSATNode.rank] at hpos
    omega
  simp [CNFSATNode.rank, CNFSATNode.extend, hlt]
  omega

/-! ## Decision oracle and concrete P685 instance -/

/-- A correct SAT decision oracle on partial CNF nodes.  This is the exact
remaining algorithmic debt: a `P = NP` claim would need such an oracle with a
polynomial implementation, or a clean phase theorem producing it. -/
structure CNFSATDecisionOracle {n : Nat} (formula : CNFFormula n) where
  decider : CNFSATNode n -> Bool
  correct :
    ∀ x : CNFSATNode n,
      decider x = true ↔ ∃ assignment : Nat -> Bool,
        CNFSATVerify formula x assignment

/-- Terminal witness selection for a fully assigned node.  It uses the same
logical verifier predicate and does not add an algorithmic claim. -/
def cnfTerminal {n : Nat} (formula : CNFFormula n)
    (x : CNFSATNode n) : Option (Nat -> Bool) := by
  classical
  exact
    if h : ∃ assignment : Nat -> Bool, CNFSATVerify formula x assignment then
      some (Classical.choose h)
    else
      none

/-- THEOREM 4: terminal witness selection is sound. -/
theorem cnfTerminal_sound {n : Nat} (formula : CNFFormula n)
    {x : CNFSATNode n} {assignment : Nat -> Bool} :
    cnfTerminal formula x = some assignment ->
      CNFSATVerify formula x assignment := by
  classical
  intro hterm
  by_cases h : ∃ assignment : Nat -> Bool, CNFSATVerify formula x assignment
  · have hsome : some (Classical.choose h) = some assignment := by
      simpa [cnfTerminal, h] using hterm
    have heq : Classical.choose h = assignment := by
      simpa using Option.some.inj hsome
    rw [← heq]
    exact Classical.choose_spec h
  · have : False := by
      simp [cnfTerminal, h] at hterm
    exact False.elim this

/-- THEOREM 5: terminal witness selection is complete whenever a verifier
witness exists. -/
theorem cnfTerminal_complete {n : Nat} (formula : CNFFormula n)
    {x : CNFSATNode n} :
    x.rank = 0 ->
      (∃ assignment : Nat -> Bool, CNFSATVerify formula x assignment) ->
        ∃ assignment : Nat -> Bool,
          cnfTerminal formula x = some assignment /\
            CNFSATVerify formula x assignment := by
  classical
  intro _hrank hex
  refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
  simp [cnfTerminal, hex]

/-- THEOREM 6: a correct CNF SAT decision oracle yields the concrete P685
binary self-reduction instance. -/
def cnfBinarySelfReduction {n : Nat} (formula : CNFFormula n)
    (oracle : CNFSATDecisionOracle formula) :
    BinarySelfReduction (CNFSATNode n) (Nat -> Bool) where
  verify := CNFSATVerify formula
  decider := oracle.decider
  decider_correct := oracle.correct
  rank := CNFSATNode.rank
  terminal := cnfTerminal formula
  terminal_sound := by
    intro x assignment hterm
    exact cnfTerminal_sound formula hterm
  terminal_complete := by
    intro x hrank hex
    exact cnfTerminal_complete formula hrank hex
  left := CNFSATNode.left
  right := CNFSATNode.right
  left_sound := by
    intro x assignment h
    exact cnfSATVerify_extend_sound formula x false assignment h
  right_sound := by
    intro x assignment h
    exact cnfSATVerify_extend_sound formula x true assignment h
  child_complete := by
    intro x hpos hex
    rcases hex with ⟨assignment, hverify⟩
    cases hbit : assignment x.depth
    · left
      exact ⟨assignment,
        cnfSATVerify_extend_complete formula x false assignment hpos hbit hverify⟩
    · right
      exact ⟨assignment,
        cnfSATVerify_extend_complete formula x true assignment hpos hbit hverify⟩
  rank_left_lt := by
    intro x hpos
    exact cnfSATNode_rank_extend_lt x false hpos
  rank_right_lt := by
    intro x hpos
    exact cnfSATNode_rank_extend_lt x true hpos

/-- THEOREM 7: the concrete CNF self-reduction compiles to the P684 witness
producer projection. -/
def cnfWitnessProducerProjection {n : Nat} (formula : CNFFormula n)
    (oracle : CNFSATDecisionOracle formula) :
    WitnessProducerProjection (CNFSATNode n) (Nat -> Bool) :=
  (cnfBinarySelfReduction formula oracle).toWitnessProducerProjection

/-- THEOREM 8: on any partial CNF node, produced verified assignment iff a
verifier assignment exists. -/
theorem cnfProducedVerifiedWitness_iff_hasWitness {n : Nat}
    (formula : CNFFormula n) (oracle : CNFSATDecisionOracle formula)
    (x : CNFSATNode n) :
    (cnfWitnessProducerProjection formula oracle).ProducedVerifiedWitness x ↔
      ∃ assignment : Nat -> Bool, CNFSATVerify formula x assignment := by
  exact
    (cnfBinarySelfReduction formula oracle).producedVerifiedWitness_iff_hasWitness x

/-- THEOREM 9: at the root, verifier witnesses are exactly satisfying
assignments for the CNF formula. -/
theorem cnfRoot_hasWitness_iff_satisfiable {n : Nat}
    (formula : CNFFormula n) :
    (∃ assignment : Nat -> Bool,
      CNFSATVerify formula (CNFSATNode.root n) assignment) ↔
        CNFSatisfiable formula := by
  constructor
  · rintro ⟨assignment, hverify⟩
    exact ⟨assignment, hverify.1⟩
  · rintro ⟨assignment, hformula⟩
    refine ⟨assignment, hformula, ?_⟩
    intro i hi
    simp [CNFSATNode.root] at hi

/-- THEOREM 10: at the root, the oracle-driven producer emits a verified
assignment iff the CNF formula is satisfiable. -/
theorem cnfRootProducedVerifiedWitness_iff_satisfiable {n : Nat}
    (formula : CNFFormula n) (oracle : CNFSATDecisionOracle formula) :
    (cnfWitnessProducerProjection formula oracle).ProducedVerifiedWitness
        (CNFSATNode.root n) ↔
      CNFSatisfiable formula := by
  rw [cnfProducedVerifiedWitness_iff_hasWitness]
  exact cnfRoot_hasWitness_iff_satisfiable formula

/-! ## Packaged certificate -/

/-- P687 certificate: the finite CNF/SAT surface is a concrete instance of the
P685 self-reduction producer theorem. -/
structure CNFSATSelfReductionCertificate where
  p686_clean_phase_root :
    CleanConsolidationPhaseProducerCertificate.{0, 0, 0}
  to_binary_self_reduction :
    ∀ {n : Nat} (formula : CNFFormula n)
      (_ : CNFSATDecisionOracle formula),
      BinarySelfReduction (CNFSATNode n) (Nat -> Bool)
  root_producer_iff_satisfiable :
    ∀ {n : Nat} (formula : CNFFormula n)
      (oracle : CNFSATDecisionOracle formula),
      (cnfWitnessProducerProjection formula oracle).ProducedVerifiedWitness
          (CNFSATNode.root n) ↔
        CNFSatisfiable formula

/-- DEFINITION 1: canonical P687 finite CNF self-reduction certificate. -/
def cnfSATSelfReductionCertificate :
    CNFSATSelfReductionCertificate where
  p686_clean_phase_root := cleanConsolidationPhaseProducerCertificate
  to_binary_self_reduction := by
    intro n formula oracle
    exact cnfBinarySelfReduction formula oracle
  root_producer_iff_satisfiable := by
    intro n formula oracle
    exact cnfRootProducedVerifiedWitness_iff_satisfiable formula oracle

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P687 grand root: P686's clean phase producer theorem plus a concrete finite
CNF/SAT self-reduction instance.

This closes the *syntax-level* SAT instantiation of P685.  It still does not
prove `P = NP`: the oracle's polynomial implementation, or a concrete clean
phase producer replacing that oracle, remains the real algorithmic debt.
-/
structure CNFSATSelfReductionUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p686_root :
    CleanConsolidationPhaseUnifiedRootCertificate.{u, v, w, z} E
  cnf_sat_self_reduction :
    CNFSATSelfReductionCertificate

/-- THEOREM 11: the finite CNF/SAT self-reduction unified root is inhabited. -/
def cnfSATSelfReductionUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CNFSATSelfReductionUnifiedRootCertificate.{u, v, w, z} E where
  p686_root := cleanConsolidationPhaseUnifiedRootCertificate (E := E)
  cnf_sat_self_reduction := cnfSATSelfReductionCertificate

end GrandUnification

end SaturationMonoid
