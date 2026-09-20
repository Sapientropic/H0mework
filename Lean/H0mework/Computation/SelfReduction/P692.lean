import H0mework.Realization.Relations.P116
import H0mework.Computation.SelfReduction.P691

/-!
# Proposition 692: layered obstruction elimination for SAT

P691 corrected the solver surface to multi-path bumpSat plus satOr merge.  The
next correction is that the solver should not repair all clauses at once.  It
should peel off exact layers:

* variables whose interaction phase is path-additive are exact/commuting;
* exact variables can be fixed/eliminated by a certified layer step;
* the remaining non-additive variables are the H¹ obstruction subproblem;
* the terminal obstruction subproblem is then handed to the P691 multi-path
  merge producer.

This file formalizes that certificate shape.  It does not implement a concrete
unit-propagation / pure-literal engine; instead it states the exact proof
obligations that such an engine must emit: rank shrinkage, satisfiability
reflection to the residual formula, and witness lifting back to the original
formula.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

set_option linter.checkUnivs false

universe u

/-! ## Exact versus obstructed variables via P116 -/

/-- A phase cochain attached to each Boolean variable.  The index set is the
local chart / interaction cover; coefficients are integer phases. -/
abbrev CNFVariablePhase (n : Nat) (Index : Type u) :=
  Fin n -> Index -> Index -> Int

/-- One certified layer-elimination summary from an original formula to a
terminal obstruction formula. -/
structure CNFLayeredObstructionElimination {n : Nat}
    (formula : CNFFormula n) (Index : Type u) [Inhabited Index] where
  terminalFormula : CNFFormula n
  phase : CNFVariablePhase n Index
  layerCount : Nat
  initialObstructionRank : Nat
  terminalObstructionRank : Nat
  rank_nonincreasing :
    terminalObstructionRank ≤ initialObstructionRank
  rank_strict_if_layered :
    layerCount ≠ 0 -> terminalObstructionRank < initialObstructionRank
  liftAssignment : (Nat -> Bool) -> Nat -> Bool
  terminal_to_initial_verify :
    ∀ assignment : Nat -> Bool,
      CNFSATVerify terminalFormula (CNFSATNode.root n) assignment ->
        CNFSATVerify formula (CNFSATNode.root n) (liftAssignment assignment)
  initial_to_terminal_satisfiable :
    CNFSatisfiable formula -> CNFSatisfiable terminalFormula

namespace CNFLayeredObstructionElimination

variable {n : Nat} {formula : CNFFormula n} {Index : Type u}
variable [Inhabited Index]
variable (L : CNFLayeredObstructionElimination formula Index)

/-- Exact variables are the path-additive variables in the P116 sense. -/
def ExactVariable (v : Fin n) : Prop :=
  PathAdditive (L.phase v)

/-- Obstructed variables are precisely the non-additive remainder. -/
def ObstructedVariable (v : Fin n) : Prop :=
  Not (L.ExactVariable v)

/-- THEOREM 1: exact/path-additive variables carry no nontrivial H¹
obstruction. -/
theorem exactVariable_not_h1 (v : Fin n)
    (hExact : L.ExactVariable v) :
    Not (CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index Int) (L.phase v)) := by
  intro hH1
  exact ((h1Obstruction_iff_not_pathAdditive (L.phase v)).mp hH1)
    hExact

/-- THEOREM 2: obstructed variables are exactly nontrivial H¹ classes. -/
theorem obstructedVariable_iff_h1 (v : Fin n) :
    L.ObstructedVariable v ↔
      CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index Int) (L.phase v) := by
  constructor
  · intro hObs
    exact (h1Obstruction_iff_not_pathAdditive (L.phase v)).mpr hObs
  · intro hH1
    exact (h1Obstruction_iff_not_pathAdditive (L.phase v)).mp hH1

/-- THEOREM 3: every variable is either exact or obstructed. -/
theorem exact_or_obstructed (v : Fin n) :
    L.ExactVariable v ∨ L.ObstructedVariable v := by
  by_cases h : L.ExactVariable v
  · exact Or.inl h
  · exact Or.inr h

/-! ## Residual satisfiability and witness lifting -/

/-- THEOREM 4: a satisfying assignment for the terminal obstruction formula
lifts to one for the original formula. -/
theorem satisfiable_of_terminal_satisfiable
    (h : CNFSatisfiable L.terminalFormula) :
    CNFSatisfiable formula := by
  rcases h with ⟨assignment, hEval⟩
  have hVerify :
      CNFSATVerify L.terminalFormula (CNFSATNode.root n) assignment := by
    constructor
    · exact hEval
    · intro i hi
      simp [CNFSATNode.root] at hi
  have hLift := L.terminal_to_initial_verify assignment hVerify
  exact (cnfRoot_hasWitness_iff_satisfiable formula).1
    ⟨L.liftAssignment assignment, hLift⟩

/-- THEOREM 5: layered exact elimination preserves satisfiability. -/
theorem satisfiable_iff_terminal_satisfiable :
    CNFSatisfiable formula ↔ CNFSatisfiable L.terminalFormula := by
  constructor
  · exact L.initial_to_terminal_satisfiable
  · exact L.satisfiable_of_terminal_satisfiable

/-- THEOREM 6: after at least one layer is peeled, the obstruction rank is
strictly smaller. -/
theorem rank_decreases_of_layered (h : L.layerCount ≠ 0) :
    L.terminalObstructionRank < L.initialObstructionRank :=
  L.rank_strict_if_layered h

/-! ## Handoff to P691 multi-path satOr merge -/

/-- If the terminal obstruction subproblem has a P691 multi-path merge
certificate, the original problem inherits a P684 root producer by lifting the
terminal witness through the layered-elimination certificate. -/
def toRootWitnessProducerProjection
    (M : CNFMultiPathSatOrMerge L.terminalFormula) :
    WitnessProducerProjection Unit (Nat -> Bool) where
  verify := fun _ assignment =>
    CNFSATVerify formula (CNFSATNode.root n) assignment
  producer := fun _ =>
    match M.rootProducer with
    | some assignment => some (L.liftAssignment assignment)
    | none => none
  sound := by
    intro _ assignment h
    cases hprod : M.rootProducer with
    | none =>
        simp [hprod] at h
    | some terminalAssignment =>
        have heq : L.liftAssignment terminalAssignment = assignment := by
          simpa [hprod] using h
        rw [← heq]
        exact L.terminal_to_initial_verify terminalAssignment
          (M.rootProducer_sound hprod)
  complete := by
    intro _ h
    have hsFormula : CNFSatisfiable formula :=
      (cnfRoot_hasWitness_iff_satisfiable formula).1 h
    have hsTerminal : CNFSatisfiable L.terminalFormula :=
      L.initial_to_terminal_satisfiable hsFormula
    rcases M.rootProducer_complete hsTerminal with
      ⟨terminalAssignment, hEmit⟩
    exact ⟨L.liftAssignment terminalAssignment, by simp [hEmit]⟩

/-- THEOREM 7: layered obstruction elimination plus terminal P691 merge emits
a verified witness iff the original CNF formula is satisfiable. -/
theorem producedVerifiedWitness_iff_satisfiable
    (M : CNFMultiPathSatOrMerge L.terminalFormula) :
    (L.toRootWitnessProducerProjection M).ProducedVerifiedWitness () ↔
      CNFSatisfiable formula := by
  rw [(L.toRootWitnessProducerProjection M).producedVerifiedWitness_iff_hasWitness]
  exact cnfRoot_hasWitness_iff_satisfiable formula

end CNFLayeredObstructionElimination

/-! ## Packaged certificate -/

/-- P692 certificate: P116 exact/non-exact phase splitting can be used as a
layered SAT preprocessor, and the terminal obstruction problem can be handed to
P691. -/
structure LayeredObstructionEliminationSATCertificate where
  p691_multi_path_root :
    MultiPathSatOrSATCertificate
  exact_no_h1 :
    ∀ {n : Nat} {formula : CNFFormula n} {Index : Type u}
      [Inhabited Index]
      (L : CNFLayeredObstructionElimination formula Index)
      (v : Fin n),
      L.ExactVariable v ->
        Not (CechAdditiveCover.H1Obstruction
          (identityPairZeroTripleCover Index Int) (L.phase v))
  obstructed_iff_h1 :
    ∀ {n : Nat} {formula : CNFFormula n} {Index : Type u}
      [Inhabited Index]
      (L : CNFLayeredObstructionElimination formula Index)
      (v : Fin n),
      L.ObstructedVariable v ↔
        CechAdditiveCover.H1Obstruction
          (identityPairZeroTripleCover Index Int) (L.phase v)
  terminal_iff_original :
    ∀ {n : Nat} {formula : CNFFormula n} {Index : Type u}
      [Inhabited Index]
      (L : CNFLayeredObstructionElimination formula Index),
      CNFSatisfiable formula ↔ CNFSatisfiable L.terminalFormula
  to_root_projection :
    ∀ {n : Nat} {formula : CNFFormula n} {Index : Type u}
      [Inhabited Index]
      (L : CNFLayeredObstructionElimination formula Index)
      (_ : CNFMultiPathSatOrMerge L.terminalFormula),
      WitnessProducerProjection Unit (Nat -> Bool)
  root_producer_iff_satisfiable :
    ∀ {n : Nat} {formula : CNFFormula n} {Index : Type u}
      [Inhabited Index]
      (L : CNFLayeredObstructionElimination formula Index)
      (M : CNFMultiPathSatOrMerge L.terminalFormula),
      (L.toRootWitnessProducerProjection M).ProducedVerifiedWitness () ↔
        CNFSatisfiable formula

/-- DEFINITION 1: canonical P692 layered obstruction-elimination certificate.
-/
def layeredObstructionEliminationSATCertificate :
    LayeredObstructionEliminationSATCertificate where
  p691_multi_path_root := multiPathSatOrSATCertificate
  exact_no_h1 := by
    intro n formula Index _ L v hExact
    exact L.exactVariable_not_h1 v hExact
  obstructed_iff_h1 := by
    intro n formula Index _ L v
    exact L.obstructedVariable_iff_h1 v
  terminal_iff_original := by
    intro n formula Index _ L
    exact L.satisfiable_iff_terminal_satisfiable
  to_root_projection := by
    intro n formula Index _ L M
    exact L.toRootWitnessProducerProjection M
  root_producer_iff_satisfiable := by
    intro n formula Index _ L M
    exact L.producedVerifiedWitness_iff_satisfiable M

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P692 grand root: layered exact/obstruction elimination sits before the
P691 multi-path satOr merge and is governed by P116 exactness/nontrivial-H¹.
-/
structure LayeredObstructionEliminationSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p691_root :
    MultiPathSatOrSATUnifiedRootCertificate.{u, v, w, z} E0
  layered_elimination :
    LayeredObstructionEliminationSATCertificate.{v}

/-- THEOREM 8: the layered-obstruction SAT unified root is inhabited. -/
def layeredObstructionEliminationSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    LayeredObstructionEliminationSATUnifiedRootCertificate.{u, v, w, z} E0 where
  p691_root := multiPathSatOrSATUnifiedRootCertificate (E0 := E0)
  layered_elimination := layeredObstructionEliminationSATCertificate

end GrandUnification

end SaturationMonoid
