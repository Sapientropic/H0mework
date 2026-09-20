import H0mework.Computation.SelfReduction.P699

/-!
# Proposition 700: threshold collapse gate for certified phase dissipation

P699 gives the finite-threshold form of the certified residual reducer: for
`0 < sigma < 1`, every clause residual eventually enters any chosen absolute
threshold band.  This file adds the runtime gate that is allowed to fire once
that band is certified.

The gate is intentionally explicit.  The continuous reducer does not generally
hit exact zero in finite time.  A runtime threshold policy may, however,
collapse a state whose residuals are all below `delta` into the zero-residual
surface.  P698 then proves that this collapsed state is fixed by the certified
dissipative phase step.

Boundary: this is a certified threshold-collapse surface.  It does not prove
that an arbitrary SAT runtime implements this policy, does not prove absence of
metastable states before the gate, does not give a polynomial bound, and does
not prove `P = NP`.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Threshold gate and collapse map -/

/-- A runtime threshold gate: all clause obstruction residuals are below a
chosen absolute tolerance `delta`. -/
def SATPhaseFlowThresholdGate
    {Clause Var : Type*} [Fintype Clause]
    (delta : ℝ) (S : SATPhaseFlowState Clause Var) : Prop :=
  0 < delta ∧ ∀ c : Clause, |S.obstruction c| < delta

/-- Collapse a threshold-certified phase-flow state to the exact
zero-obstruction surface, preserving the current variable angles. -/
def phaseFlowThresholdCollapse
    {Clause Var : Type*} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) : SATPhaseFlowState Clause Var where
  theta := S.theta
  obstruction := fun _ => 0

/-- THEOREM 1: threshold collapse preserves variable angles. -/
theorem phaseFlowThresholdCollapse_theta
    {Clause Var : Type*} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) (i : Var) :
    (phaseFlowThresholdCollapse S).theta i = S.theta i := rfl

/-- THEOREM 2: threshold collapse zeros every obstruction residual. -/
theorem phaseFlowThresholdCollapse_obstruction
    {Clause Var : Type*} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) (c : Clause) :
    (phaseFlowThresholdCollapse S).obstruction c = 0 := rfl

/-- THEOREM 3: threshold collapse lands exactly on the zero-energy surface. -/
theorem phaseFlowThresholdCollapse_energy_zero
    {Clause Var : Type*} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) :
    (phaseFlowThresholdCollapse S).energy = 0 := by
  classical
  apply (phaseResidualEnergy_eq_zero_iff
    (phaseFlowThresholdCollapse S).obstruction).2
  intro c
  rfl

/-! ## Gate certificates supplied by energy / pointwise bounds -/

/-- THEOREM 4: an energy bound below `delta^2` gives the threshold gate. -/
theorem thresholdGate_of_energy_lt_sq
    {Clause Var : Type*} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) {delta : ℝ}
    (hδ : 0 < delta) (hE : S.energy < delta ^ 2) :
    SATPhaseFlowThresholdGate delta S := by
  constructor
  · exact hδ
  · intro c
    exact abs_residual_lt_of_phaseResidualEnergy_lt_sq
      S.obstruction hδ (by simpa [SATPhaseFlowState.energy] using hE) c

/-- THEOREM 5: pointwise residual control is exactly the runtime gate payload. -/
theorem thresholdGate_of_pointwise_abs
    {Clause Var : Type*} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) {delta : ℝ}
    (hδ : 0 < delta) (hpoint : ∀ c : Clause, |S.obstruction c| < delta) :
    SATPhaseFlowThresholdGate delta S :=
  ⟨hδ, hpoint⟩

/-- THEOREM 6: P699 eventually supplies the threshold gate for every positive
`delta` along the certified dissipative phase-flow iterate. -/
theorem eventually_thresholdGate_phaseFlowDissipationIterate
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (delta : ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1) (hδ : 0 < delta) :
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      SATPhaseFlowThresholdGate delta
        (phaseFlowDissipationIterate sigma dt direction n S) := by
  classical
  rcases eventually_abs_phaseFlowDissipationIterate_obstruction_lt
      sigma dt direction S delta h0 h1 hδ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact thresholdGate_of_pointwise_abs
    (phaseFlowDissipationIterate sigma dt direction n S) hδ (hN n hn)

/-! ## Collapse target is fixed -/

/-- THEOREM 7: after threshold collapse, the certified dissipative step is
exactly fixed. -/
theorem phaseFlowThresholdCollapse_fixed
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var) :
    phaseFlowDissipationStep sigma dt direction
        (phaseFlowThresholdCollapse S) =
      phaseFlowThresholdCollapse S := by
  exact phaseFlowDissipationStep_fixed_of_energy_zero
    sigma dt direction (phaseFlowThresholdCollapse S)
    (phaseFlowThresholdCollapse_energy_zero S)

/-- THEOREM 8: after enough certified dissipative phase-flow steps, the
threshold gate is available; firing it lands on a fixed zero-obstruction state. -/
theorem eventually_thresholdGate_and_collapse_fixed
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (delta : ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1) (hδ : 0 < delta) :
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      SATPhaseFlowThresholdGate delta
          (phaseFlowDissipationIterate sigma dt direction n S) ∧
        phaseFlowDissipationStep sigma dt direction
            (phaseFlowThresholdCollapse
              (phaseFlowDissipationIterate sigma dt direction n S)) =
          phaseFlowThresholdCollapse
            (phaseFlowDissipationIterate sigma dt direction n S) := by
  classical
  rcases eventually_thresholdGate_phaseFlowDissipationIterate
      sigma dt direction S delta h0 h1 hδ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  constructor
  · exact hN n hn
  · exact phaseFlowThresholdCollapse_fixed
      sigma dt direction
      (phaseFlowDissipationIterate sigma dt direction n S)

/-! ## Certificate packaging -/

/-- P700 certificate: the P699 finite-threshold entry can be turned into an
explicit zero-residual collapse gate whose target is fixed by P698. -/
structure SATPhaseFlowThresholdCollapseCertificate : Prop where
  p699_epsilon_threshold :
    SATPhaseFlowEpsilonThresholdCertificate.{u, v}
  collapse_preserves_theta :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : SATPhaseFlowState Clause Var) (i : Var),
      (phaseFlowThresholdCollapse S).theta i = S.theta i
  collapse_zeroes_obstruction :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : SATPhaseFlowState Clause Var) (c : Clause),
      (phaseFlowThresholdCollapse S).obstruction c = 0
  collapse_energy_zero :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : SATPhaseFlowState Clause Var),
      (phaseFlowThresholdCollapse S).energy = 0
  threshold_gate_of_energy :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : SATPhaseFlowState Clause Var) {delta : ℝ},
      0 < delta -> S.energy < delta ^ 2 ->
        SATPhaseFlowThresholdGate delta S
  eventually_threshold_gate :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var)
      (delta : ℝ),
      0 < sigma -> sigma < 1 -> 0 < delta ->
        ∃ N : ℕ, ∀ n : ℕ, N <= n ->
          SATPhaseFlowThresholdGate delta
            (phaseFlowDissipationIterate sigma dt direction n S)
  collapse_fixed :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var),
      phaseFlowDissipationStep sigma dt direction
          (phaseFlowThresholdCollapse S) =
        phaseFlowThresholdCollapse S
  eventually_threshold_gate_and_collapse_fixed :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var)
      (delta : ℝ),
      0 < sigma -> sigma < 1 -> 0 < delta ->
        ∃ N : ℕ, ∀ n : ℕ, N <= n ->
          SATPhaseFlowThresholdGate delta
              (phaseFlowDissipationIterate sigma dt direction n S) ∧
            phaseFlowDissipationStep sigma dt direction
                (phaseFlowThresholdCollapse
                  (phaseFlowDissipationIterate sigma dt direction n S)) =
              phaseFlowThresholdCollapse
                (phaseFlowDissipationIterate sigma dt direction n S)

/-- DEFINITION 1: canonical P700 threshold-collapse certificate. -/
def satPhaseFlowThresholdCollapseCertificate :
    SATPhaseFlowThresholdCollapseCertificate.{u, v} where
  p699_epsilon_threshold := satPhaseFlowEpsilonThresholdCertificate
  collapse_preserves_theta := by
    intro Clause Var _ S i
    exact phaseFlowThresholdCollapse_theta S i
  collapse_zeroes_obstruction := by
    intro Clause Var _ S c
    exact phaseFlowThresholdCollapse_obstruction S c
  collapse_energy_zero := by
    intro Clause Var _ S
    exact phaseFlowThresholdCollapse_energy_zero S
  threshold_gate_of_energy := by
    intro Clause Var _ S delta hδ hE
    exact thresholdGate_of_energy_lt_sq S hδ hE
  eventually_threshold_gate := by
    intro Clause Var _ sigma dt direction S delta h0 h1 hδ
    exact eventually_thresholdGate_phaseFlowDissipationIterate
      sigma dt direction S delta h0 h1 hδ
  collapse_fixed := by
    intro Clause Var _ sigma dt direction S
    exact phaseFlowThresholdCollapse_fixed sigma dt direction S
  eventually_threshold_gate_and_collapse_fixed := by
    intro Clause Var _ sigma dt direction S delta h0 h1 hδ
    exact eventually_thresholdGate_and_collapse_fixed
      sigma dt direction S delta h0 h1 hδ

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

/-- P700 grand root: P699 plus an explicit runtime threshold-collapse gate into
the P698 fixed zero-obstruction surface. -/
structure PhaseFlowThresholdCollapseUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p699_root :
    PhaseFlowEpsilonThresholdUnifiedRootCertificate.{u, v, w, z} E0
  threshold_collapse_surface :
    SATPhaseFlowThresholdCollapseCertificate.{v, w}

/-- THEOREM 9: the phase-flow threshold-collapse unified root is inhabited. -/
def phaseFlowThresholdCollapseUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    PhaseFlowThresholdCollapseUnifiedRootCertificate.{u, v, w, z} E0 where
  p699_root := phaseFlowEpsilonThresholdUnifiedRootCertificate (E0 := E0)
  threshold_collapse_surface := satPhaseFlowThresholdCollapseCertificate

end GrandUnification

end SaturationMonoid
