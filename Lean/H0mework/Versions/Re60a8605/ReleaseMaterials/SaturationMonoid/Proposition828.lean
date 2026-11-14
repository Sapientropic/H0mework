import H0mework.Computation.SelfReduction.P703

/-!
# Proposition 828: real CNF semantics produce the phase residual carrier

P698/P703 proved that finite SAT/Hamiltonian energy is exactly squared
obstruction energy on a residual carrier.  This file connects that carrier to
the concrete CNF syntax from P687 instead of leaving the residual vector
abstract.

For a concrete formula and assignment, the clause index `i : Fin formula.length`
is the finite carrier coordinate.  Its residual is

* `0` when the indexed clause is satisfied;
* `1` when the indexed clause is not satisfied.

Therefore formula satisfaction is exactly pointwise zero residual, exactly zero
Lyapunov/Hamiltonian energy, and, for an active residual transport
`sigma ≠ 0`, exactly the fixed-point surface of the certified dissipative phase
step.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Concrete CNF residual state -/

/-- The concrete residual coordinate for the indexed clause of a CNF formula. -/
def CNFIndexedClauseResidual {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool) :
    Fin formula.length -> ℝ :=
  fun i => if CNFClause.eval (formula.get i) assignment = true then 0 else 1

/-- The phase angle readout induced by a Boolean assignment. -/
def CNFAssignmentPhaseTheta {n : Nat}
    (assignment : Nat -> Bool) : Fin n -> ℝ :=
  fun i => if assignment i.val then trueAngle else falseAngle

/-- The concrete phase residual state produced by a CNF formula and a Boolean
assignment.  Variables carry assignment angles; clauses carry semantic residuals.
-/
def CNFPhaseResidualState {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool) :
    SATPhaseFlowState (Fin formula.length) (Fin n) where
  theta := CNFAssignmentPhaseTheta assignment
  obstruction := CNFIndexedClauseResidual formula assignment

/-! ## CNF truth is residual zero -/

/-- THEOREM 1: formula truth is equivalent to every indexed clause being true. -/
theorem cnfFormula_eval_true_iff_indexed_clauses {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool) :
    CNFFormula.eval formula assignment = true ↔
      ∀ i : Fin formula.length,
        CNFClause.eval (formula.get i) assignment = true := by
  rw [CNFFormula.eval, List.all_eq_true]
  constructor
  · intro hall i
    exact hall (formula.get i) (List.get_mem formula i)
  · intro hidx clause hmem
    rcases List.get_of_mem hmem with ⟨i, hi⟩
    simpa [← hi] using hidx i

/-- THEOREM 2: an indexed clause residual is zero exactly when that concrete
clause is satisfied. -/
theorem cnfIndexedClauseResidual_eq_zero_iff_clause_eval {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool)
    (i : Fin formula.length) :
    CNFIndexedClauseResidual formula assignment i = 0 ↔
      CNFClause.eval (formula.get i) assignment = true := by
  by_cases h : CNFClause.eval (formula.get i) assignment = true
  · simp [CNFIndexedClauseResidual]
  · have hfalse : CNFClause.eval (formula.get i) assignment = false := by
      cases hval : CNFClause.eval (formula.get i) assignment
      · rfl
      · exact False.elim (h hval)
    simp [CNFIndexedClauseResidual]

/-- THEOREM 3: formula truth is exactly pointwise-zero concrete residual. -/
theorem cnfFormula_eval_true_iff_indexed_residual_zero {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool) :
    CNFFormula.eval formula assignment = true ↔
      ∀ i : Fin formula.length,
        CNFIndexedClauseResidual formula assignment i = 0 := by
  rw [cnfFormula_eval_true_iff_indexed_clauses]
  constructor
  · intro hall i
    exact (cnfIndexedClauseResidual_eq_zero_iff_clause_eval
      formula assignment i).2 (hall i)
  · intro hzero i
    exact (cnfIndexedClauseResidual_eq_zero_iff_clause_eval
      formula assignment i).1 (hzero i)

/-! ## CNF truth is zero SAT/Hamiltonian energy -/

/-- THEOREM 4: concrete CNF residual energy is zero exactly when the assignment
satisfies the formula. -/
theorem cnfIndexedResidualEnergy_zero_iff_formula_eval {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool) :
    phaseResidualEnergy (CNFIndexedClauseResidual formula assignment) = 0 ↔
      CNFFormula.eval formula assignment = true := by
  rw [phaseResidualEnergy_eq_zero_iff]
  exact Iff.symm
    (cnfFormula_eval_true_iff_indexed_residual_zero formula assignment)

/-- THEOREM 5: the concrete CNF phase-state energy is zero exactly when the
assignment satisfies the formula. -/
theorem cnfPhaseResidualState_energy_zero_iff_formula_eval {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool) :
    (CNFPhaseResidualState formula assignment).energy = 0 ↔
      CNFFormula.eval formula assignment = true := by
  simpa [CNFPhaseResidualState, SATPhaseFlowState.energy] using
    cnfIndexedResidualEnergy_zero_iff_formula_eval formula assignment

/-- THEOREM 6: the Hamiltonian-facing energy readout of the concrete CNF phase
state is zero exactly when the assignment satisfies the formula. -/
theorem cnfPhaseResidualState_hamiltonianEnergy_zero_iff_formula_eval {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool) :
    hamiltonianEnergyReadout (CNFPhaseResidualState formula assignment) = 0 ↔
      CNFFormula.eval formula assignment = true := by
  simpa [hamiltonianEnergyReadout, CNFPhaseResidualState] using
    cnfIndexedResidualEnergy_zero_iff_formula_eval formula assignment

/-! ## Active residual transport fixes exactly satisfying CNF states -/

/-- THEOREM 7: under an active residual transport (`sigma ≠ 0`), the concrete
CNF phase state is a fixed point of the certified dissipative phase step exactly
when the assignment satisfies the formula.

The reverse direction is not a tautology over an abstract zero state: fixedness
forces each concrete clause residual to obey `(1 - sigma) r = r`, hence
`sigma * r = 0`, and activity forces `r = 0`. -/
theorem cnfPhaseResidualState_dissipationStep_fixed_iff_formula_eval_of_sigma_ne_zero
    {n : Nat}
    (formula : CNFFormula n) (assignment : Nat -> Bool)
    (sigma dt : ℝ)
    (direction : Fin formula.length -> Fin n -> ℝ)
    (hsigma : sigma ≠ 0) :
    phaseFlowDissipationStep sigma dt direction
        (CNFPhaseResidualState formula assignment) =
      CNFPhaseResidualState formula assignment ↔
        CNFFormula.eval formula assignment = true := by
  constructor
  · intro hfixed
    have hobfun := congrArg SATPhaseFlowState.obstruction hfixed
    have hzero :
        ∀ i : Fin formula.length,
          CNFIndexedClauseResidual formula assignment i = 0 := by
      intro i
      have hi :
          phaseResidualRelaxStep sigma
              (CNFIndexedClauseResidual formula assignment) i =
            CNFIndexedClauseResidual formula assignment i := by
        simpa [phaseFlowDissipationStep, CNFPhaseResidualState] using
          congrFun hobfun i
      have hmul :
          sigma * CNFIndexedClauseResidual formula assignment i = 0 := by
        dsimp [phaseResidualRelaxStep] at hi
        nlinarith
      exact (mul_eq_zero.mp hmul).resolve_left hsigma
    exact (cnfFormula_eval_true_iff_indexed_residual_zero
      formula assignment).2 hzero
  · intro hsat
    exact phaseFlowDissipationStep_fixed_of_energy_zero
      sigma dt direction (CNFPhaseResidualState formula assignment)
      ((cnfPhaseResidualState_energy_zero_iff_formula_eval
        formula assignment).2 hsat)

/-! ## Certificate packaging -/

/-- P828 certificate: real CNF clause semantics produce the finite phase
residual carrier used by P698/P703. -/
structure RealCNFPhaseResidualProducerCertificate : Prop where
  clause_residual_zero_iff_clause_satisfied :
    ∀ {n : Nat} (formula : CNFFormula n) (assignment : Nat -> Bool)
      (i : Fin formula.length),
      CNFIndexedClauseResidual formula assignment i = 0 ↔
        CNFClause.eval (formula.get i) assignment = true
  formula_eval_iff_residual_zero :
    ∀ {n : Nat} (formula : CNFFormula n) (assignment : Nat -> Bool),
      CNFFormula.eval formula assignment = true ↔
        ∀ i : Fin formula.length,
          CNFIndexedClauseResidual formula assignment i = 0
  formula_eval_iff_energy_zero :
    ∀ {n : Nat} (formula : CNFFormula n) (assignment : Nat -> Bool),
      phaseResidualEnergy
          (CNFIndexedClauseResidual formula assignment) = 0 ↔
        CNFFormula.eval formula assignment = true
  formula_eval_iff_hamiltonian_energy_zero :
    ∀ {n : Nat} (formula : CNFFormula n) (assignment : Nat -> Bool),
      hamiltonianEnergyReadout
          (CNFPhaseResidualState formula assignment) = 0 ↔
        CNFFormula.eval formula assignment = true
  active_transport_fixed_iff_formula_eval :
    ∀ {n : Nat}
      (formula : CNFFormula n) (assignment : Nat -> Bool)
      (sigma dt : ℝ)
      (direction : Fin formula.length -> Fin n -> ℝ),
      sigma ≠ 0 ->
        (phaseFlowDissipationStep sigma dt direction
              (CNFPhaseResidualState formula assignment) =
            CNFPhaseResidualState formula assignment ↔
              CNFFormula.eval formula assignment = true)

/-- DEFINITION 1: canonical P828 real-CNF residual producer certificate. -/
def realCNFPhaseResidualProducerCertificate :
    RealCNFPhaseResidualProducerCertificate where
  clause_residual_zero_iff_clause_satisfied := by
    intro n formula assignment i
    exact cnfIndexedClauseResidual_eq_zero_iff_clause_eval
      formula assignment i
  formula_eval_iff_residual_zero := by
    intro n formula assignment
    exact cnfFormula_eval_true_iff_indexed_residual_zero formula assignment
  formula_eval_iff_energy_zero := by
    intro n formula assignment
    exact cnfIndexedResidualEnergy_zero_iff_formula_eval formula assignment
  formula_eval_iff_hamiltonian_energy_zero := by
    intro n formula assignment
    exact cnfPhaseResidualState_hamiltonianEnergy_zero_iff_formula_eval
      formula assignment
  active_transport_fixed_iff_formula_eval := by
    intro n formula assignment sigma dt direction
    exact cnfPhaseResidualState_dissipationStep_fixed_iff_formula_eval_of_sigma_ne_zero
      formula assignment sigma dt direction

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P828 grand root: the P703 shared Hamiltonian/SAT residual carrier is fed
by concrete CNF clause semantics. -/
structure RealCNFPhaseResidualUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p703_same_carrier :
    HamiltonianSATEnergySameCarrierUnifiedRootCertificate E
  real_cnf_residual :
    RealCNFPhaseResidualProducerCertificate

/-- THEOREM 8: the real-CNF phase residual grand root is inhabited. -/
def realCNFPhaseResidualUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    RealCNFPhaseResidualUnifiedRootCertificate E where
  p703_same_carrier :=
    hamiltonianSATEnergySameCarrierUnifiedRootCertificate (E := E)
  real_cnf_residual :=
    realCNFPhaseResidualProducerCertificate

end GrandUnification

end SaturationMonoid
