import H0mework.Realization.RelaxationFlow.P247
import H0mework.Computation.SelfReduction.P694
import H0mework.Realization.CyclicMemory.P117

/-!
# Proposition 695: SAT phase-flow surface

P694 finished the concrete unit-propagation layer.  The next solver-shaped
surface is not another discrete flip rule.  It is the phase-flow reading of
SAT variables:

* `theta = pi / 2` is the imaginary-axis / undecided state;
* `theta = 0` is the positive-real / true state;
* `theta = pi` is the negative-real / false state;
* a 3-literal clause is read as a three-agent phase ring;
* the global variable angles are an exact potential, so only the local
  non-cancelled residual contributes H1 obstruction;
* all variables move simultaneously under a vector field
  `sum obstruction_c * direction_c(i)`.

Boundary: this is a phase-flow certificate surface, not yet a convergence
theorem, not a polynomial SAT algorithm, and not a proof that every CNF's
phase flow reaches a satisfying assignment.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Boolean decisions as phase angles -/

/-- A SAT variable phase before/after consolidation to the real axis. -/
inductive SATPhaseValue where
  | undecided
  | decidedTrue
  | decidedFalse
  deriving DecidableEq, Repr

/-- The imaginary-axis angle: unresolved / virtual / undecided. -/
def undecidedAngle : ℝ := Real.pi / 2

/-- The positive-real-axis angle: Boolean true. -/
def trueAngle : ℝ := 0

/-- The negative-real-axis angle: Boolean false. -/
def falseAngle : ℝ := Real.pi

/-- Interpret a SAT phase value as its angle. -/
def SATPhaseValue.angle : SATPhaseValue -> ℝ
  | .undecided => undecidedAngle
  | .decidedTrue => trueAngle
  | .decidedFalse => falseAngle

/-- Interpret a SAT phase value as the P247 scalar phase point. -/
def SATPhaseValue.phasePoint (s : SATPhaseValue) : ℂ :=
  SaturationMonoid.AffineRelaxation.unitComplexPhaseWithRate 1 s.angle

/-- THEOREM 1: undecided variables sit at `pi / 2`, the imaginary-axis angle. -/
theorem undecided_angle :
    SATPhaseValue.angle .undecided = Real.pi / 2 := rfl

/-- THEOREM 2: decided-true variables sit on the positive real axis. -/
theorem decidedTrue_angle :
    SATPhaseValue.angle .decidedTrue = 0 := rfl

/-- THEOREM 3: decided-false variables sit on the negative real axis. -/
theorem decidedFalse_angle :
    SATPhaseValue.angle .decidedFalse = Real.pi := rfl

/-- THEOREM 4: every SAT phase point is a P247 fixed-rate scalar phase. -/
theorem satPhasePoint_is_p247_flow_point (s : SATPhaseValue) :
    s.phasePoint =
      SaturationMonoid.AffineRelaxation.unitComplexPhaseWithRate 1 s.angle :=
  rfl

/-! ## Clause rings: global angle potential plus local residual -/

/-- The global variable-angle potential as a phase cochain. -/
def anglePotentialCochain (theta : ThreeCycleTime -> ℝ) :
    ThreeCycleTime -> ThreeCycleTime -> ℝ :=
  fun i j => theta j - theta i

/-- THEOREM 5: a pure angle potential is path-additive/exact. -/
theorem anglePotentialCochain_pathAdditive
    (theta : ThreeCycleTime -> ℝ) :
    PathAdditive (anglePotentialCochain theta) := by
  intro i j k
  simp [anglePotentialCochain]

/-- THEOREM 6: a pure angle potential has zero three-agent ring residual. -/
theorem anglePotentialCochain_residual_zero
    (theta : ThreeCycleTime -> ℝ) :
    threeAgentRingResidual (anglePotentialCochain theta) = 0 := by
  simp [threeAgentRingResidual, anglePotentialCochain]

/-- A clause cochain is the exact global angle potential plus a local
interaction residual. -/
def clausePhaseCochain
    (theta : ThreeCycleTime -> ℝ)
    (localPhase : ThreeCycleTime -> ThreeCycleTime -> ℝ) :
    ThreeCycleTime -> ThreeCycleTime -> ℝ :=
  fun i j => anglePotentialCochain theta i j + localPhase i j

/-- THEOREM 7: the clause ring residual ignores the exact global-potential
part and equals the local interaction residual. -/
theorem clausePhaseCochain_residual_eq_local
    (theta : ThreeCycleTime -> ℝ)
    (localPhase : ThreeCycleTime -> ThreeCycleTime -> ℝ) :
    threeAgentRingResidual (clausePhaseCochain theta localPhase) =
      threeAgentRingResidual localPhase := by
  simp [threeAgentRingResidual, clausePhaseCochain, anglePotentialCochain]
  ring

/-- THEOREM 8: noncancelled local residual gives a genuine H1 obstruction for
the full clause phase cochain. -/
theorem clausePhaseCochain_h1_of_local_residual_nonzero
    (theta : ThreeCycleTime -> ℝ)
    (localPhase : ThreeCycleTime -> ThreeCycleTime -> ℝ)
    (hres : threeAgentRingResidual localPhase ≠ 0) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime ℝ)
      (clausePhaseCochain theta localPhase) := by
  have hfull :
      threeAgentRingResidual (clausePhaseCochain theta localPhase) ≠ 0 := by
    simpa [clausePhaseCochain_residual_eq_local theta localPhase] using hres
  exact threeAgentRingResidual_nonzero_h1
    (clausePhaseCochain theta localPhase) hfull

/-! ## Synchronous obstruction-driven phase flow -/

/-- The synchronous SAT phase-flow vector field:
`d theta_i / dt = sum_c obstruction_c * direction_c(i)`. -/
def phaseFlowVectorField {Clause Var : Type*} [Fintype Clause]
    (obstruction : Clause -> ℝ)
    (direction : Clause -> Var -> ℝ)
    (i : Var) : ℝ :=
  ∑ c, obstruction c * direction c i

/-- One explicit Euler-style phase step for the obstruction-driven flow. -/
def phaseFlowStep {Clause Var : Type*} [Fintype Clause]
    (theta : Var -> ℝ)
    (obstruction : Clause -> ℝ)
    (direction : Clause -> Var -> ℝ)
    (dt : ℝ) : Var -> ℝ :=
  fun i => theta i + dt * phaseFlowVectorField obstruction direction i

/-- THEOREM 9: if all clause obstructions vanish, the vector field is zero. -/
theorem phaseFlowVectorField_zero_of_all_obstruction_zero
    {Clause Var : Type*} [Fintype Clause]
    (obstruction : Clause -> ℝ)
    (direction : Clause -> Var -> ℝ)
    (i : Var)
    (hzero : ∀ c, obstruction c = 0) :
    phaseFlowVectorField obstruction direction i = 0 := by
  classical
  simp [phaseFlowVectorField, hzero]

/-- THEOREM 10: if all obstructions vanish, every variable phase is fixed by a
phase-flow step. -/
theorem phaseFlowStep_fixed_of_all_obstruction_zero
    {Clause Var : Type*} [Fintype Clause]
    (theta : Var -> ℝ)
    (obstruction : Clause -> ℝ)
    (direction : Clause -> Var -> ℝ)
    (dt : ℝ) (i : Var)
    (hzero : ∀ c, obstruction c = 0) :
    phaseFlowStep theta obstruction direction dt i = theta i := by
  simp [phaseFlowStep,
    phaseFlowVectorField_zero_of_all_obstruction_zero
      obstruction direction i hzero]

/-- THEOREM 11: a phase-flow step is pointwise simultaneous over variables. -/
theorem phaseFlowStep_pointwise
    {Clause Var : Type*} [Fintype Clause]
    (theta : Var -> ℝ)
    (obstruction : Clause -> ℝ)
    (direction : Clause -> Var -> ℝ)
    (dt : ℝ) (i : Var) :
    phaseFlowStep theta obstruction direction dt i =
      theta i + dt * phaseFlowVectorField obstruction direction i := rfl

/-! ## Certificate packaging -/

/-- P695 certificate: SAT variables carry the P247 phase-flow surface, and
clause H1 obstruction is exactly the non-exact local residual over a three-agent
ring. -/
structure SATPhaseFlowSurfaceCertificate : Prop where
  p247_phase_flow :
    SaturationMonoid.AffineRelaxation.ScalarPhaseFlowWithRateGeneratorCertificate ℂ
  undecided_is_pi_div_two :
    SATPhaseValue.angle .undecided = Real.pi / 2
  true_is_zero :
    SATPhaseValue.angle .decidedTrue = 0
  false_is_pi :
    SATPhaseValue.angle .decidedFalse = Real.pi
  angle_potential_exact :
    ∀ theta : ThreeCycleTime -> ℝ,
      PathAdditive (anglePotentialCochain theta)
  angle_potential_residual_zero :
    ∀ theta : ThreeCycleTime -> ℝ,
      threeAgentRingResidual (anglePotentialCochain theta) = 0
  local_residual_controls_h1 :
    ∀ (theta : ThreeCycleTime -> ℝ)
      (localPhase : ThreeCycleTime -> ThreeCycleTime -> ℝ),
      threeAgentRingResidual localPhase ≠ 0 ->
        CechAdditiveCover.H1Obstruction
          (identityPairZeroTripleCover ThreeCycleTime ℝ)
          (clausePhaseCochain theta localPhase)
  zero_obstruction_no_phase_motion :
    ∀ {Clause Var : Type*} [Fintype Clause]
      (theta : Var -> ℝ)
      (obstruction : Clause -> ℝ)
      (direction : Clause -> Var -> ℝ)
      (dt : ℝ) (i : Var),
      (∀ c, obstruction c = 0) ->
        phaseFlowStep theta obstruction direction dt i = theta i

/-- DEFINITION 1: canonical P695 phase-flow surface certificate. -/
def satPhaseFlowSurfaceCertificate :
    SATPhaseFlowSurfaceCertificate where
  p247_phase_flow :=
    SaturationMonoid.AffineRelaxation.scalarPhaseFlowWithRateGeneratorCertificate
      (E := ℂ)
  undecided_is_pi_div_two := undecided_angle
  true_is_zero := decidedTrue_angle
  false_is_pi := decidedFalse_angle
  angle_potential_exact := anglePotentialCochain_pathAdditive
  angle_potential_residual_zero := anglePotentialCochain_residual_zero
  local_residual_controls_h1 :=
    clausePhaseCochain_h1_of_local_residual_nonzero
  zero_obstruction_no_phase_motion := by
    intro Clause Var _ theta obstruction direction dt i hzero
    exact phaseFlowStep_fixed_of_all_obstruction_zero
      theta obstruction direction dt i hzero

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

/-- P695 grand root: the discrete P694/P693 preprocessing roots sit under the
P247/P117 phase-flow SAT surface. -/
structure PhaseFlowSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p694_root :
    UnitPropagationSATUnifiedRootCertificate.{u, v, w, z} E0
  phase_flow_surface :
    SATPhaseFlowSurfaceCertificate.{v, w}

/-- THEOREM 12: the phase-flow SAT unified root is inhabited. -/
def phaseFlowSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    PhaseFlowSATUnifiedRootCertificate.{u, v, w, z} E0 where
  p694_root := unitPropagationSATUnifiedRootCertificate (E0 := E0)
  phase_flow_surface := satPhaseFlowSurfaceCertificate

end GrandUnification

end SaturationMonoid
