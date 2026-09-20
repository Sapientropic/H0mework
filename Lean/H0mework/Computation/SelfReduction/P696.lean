import H0mework.Computation.SelfReduction.P695

/-!
# Proposition 696: phase residual Lyapunov dissipation

P695 formalized the virtual-axis SAT phase-flow surface:
variables move synchronously under `sum obstruction_c * direction_c(i)`, and
local clause residual is the source of the P117 H1 obstruction.

This file adds the first machine-checked Lyapunov layer for that surface.  It
does not prove convergence of arbitrary CNF phase dynamics.  It proves the
piece that a runtime can certify locally: if the clause residual vector is
consumed by the saturation law

`r_c -> (1 - sigma) * r_c`,

then the residual energy `sum_c r_c^2` is multiplied exactly by
`(1 - sigma)^2`.  Hence, for `0 <= sigma <= 1`, energy is nonincreasing, and
for `0 < sigma < 1` with nonzero residual energy, it strictly decreases.

Boundary: this is a dissipation certificate for the residual update model.  It
is not a proof that every SAT phase-flow implementation realizes this update,
not a no-metastable-state theorem, not a polynomial runtime bound, and not
`P = NP`.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Residual energy and saturation dissipation -/

/-- Saturation consumes a residual by multiplying its headroom by `1 - sigma`.
This is the residual-side face of the same affine law used throughout the
framework. -/
def phaseResidualRelaxStep {Clause : Type*}
    (sigma : ℝ) (residual : Clause -> ℝ) : Clause -> ℝ :=
  fun c => (1 - sigma) * residual c

/-- Squared residual energy over a finite clause surface. -/
def phaseResidualEnergy {Clause : Type*} [Fintype Clause]
    (residual : Clause -> ℝ) : ℝ :=
  ∑ c, (residual c) ^ 2

/-- THEOREM 1: squared residual energy is nonnegative. -/
theorem phaseResidualEnergy_nonneg {Clause : Type*} [Fintype Clause]
    (residual : Clause -> ℝ) :
    0 <= phaseResidualEnergy residual := by
  classical
  dsimp [phaseResidualEnergy]
  exact Finset.sum_nonneg (fun c _ => sq_nonneg (residual c))

/-- THEOREM 2: residual saturation multiplies energy exactly by
`(1 - sigma)^2`. -/
theorem phaseResidualEnergy_relax_eq {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (residual : Clause -> ℝ) :
    phaseResidualEnergy (phaseResidualRelaxStep sigma residual) =
      (1 - sigma) ^ 2 * phaseResidualEnergy residual := by
  classical
  dsimp [phaseResidualEnergy, phaseResidualRelaxStep]
  simp only [Finset.mul_sum]
  congr 1
  ext c
  ring

/-- THEOREM 3: if `0 <= sigma <= 1`, one residual dissipation step cannot
increase squared residual energy. -/
theorem phaseResidualEnergy_relax_nonincreasing
    {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (residual : Clause -> ℝ)
    (h0 : 0 <= sigma) (h1 : sigma <= 1) :
    phaseResidualEnergy (phaseResidualRelaxStep sigma residual) <=
      phaseResidualEnergy residual := by
  classical
  rw [phaseResidualEnergy_relax_eq]
  have hE : 0 <= phaseResidualEnergy residual :=
    phaseResidualEnergy_nonneg residual
  have hfactor : (1 - sigma) ^ 2 <= 1 := by
    nlinarith [sq_nonneg sigma, sq_nonneg (1 - sigma), h0, h1]
  have hmul :=
    mul_le_mul_of_nonneg_right hfactor hE
  simpa using hmul

/-- THEOREM 4: if `0 < sigma < 1` and residual energy is nonzero, one
dissipation step strictly decreases squared residual energy. -/
theorem phaseResidualEnergy_relax_strict
    {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (residual : Clause -> ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1)
    (hE : 0 < phaseResidualEnergy residual) :
    phaseResidualEnergy (phaseResidualRelaxStep sigma residual) <
      phaseResidualEnergy residual := by
  classical
  rw [phaseResidualEnergy_relax_eq]
  have hfactor : (1 - sigma) ^ 2 < 1 := by
    nlinarith [sq_nonneg sigma, sq_nonneg (1 - sigma), h0, h1]
  have hmul :=
    mul_lt_mul_of_pos_right hfactor hE
  simpa using hmul

/-! ## Coupling the residual dissipation to P695 phase steps -/

/-- A finite SAT phase-flow state: variable angles plus clause obstruction
residuals. -/
structure SATPhaseFlowState (Clause Var : Type*) [Fintype Clause] where
  theta : Var -> ℝ
  obstruction : Clause -> ℝ

/-- The Lyapunov energy of a phase-flow state only reads the obstruction
residuals.  The angle component may move synchronously while this energy tracks
whether the H1 residual is being consumed. -/
def SATPhaseFlowState.energy {Clause Var : Type*} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) : ℝ :=
  phaseResidualEnergy S.obstruction

/-- One certified dissipative phase step: P695's synchronous angle step plus a
saturation residual-consumption step. -/
def phaseFlowDissipationStep {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var) :
    SATPhaseFlowState Clause Var where
  theta := phaseFlowStep S.theta S.obstruction direction dt
  obstruction := phaseResidualRelaxStep sigma S.obstruction

/-- THEOREM 5: a dissipative phase step multiplies state energy by
`(1 - sigma)^2`. -/
theorem phaseFlowDissipationStep_energy_eq
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var) :
    (phaseFlowDissipationStep sigma dt direction S).energy =
      (1 - sigma) ^ 2 * S.energy := by
  classical
  dsimp [SATPhaseFlowState.energy, phaseFlowDissipationStep]
  exact phaseResidualEnergy_relax_eq sigma S.obstruction

/-- THEOREM 6: certified dissipative phase steps are Lyapunov
nonincreasing whenever `0 <= sigma <= 1`. -/
theorem phaseFlowDissipationStep_energy_nonincreasing
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (h0 : 0 <= sigma) (h1 : sigma <= 1) :
    (phaseFlowDissipationStep sigma dt direction S).energy <= S.energy := by
  classical
  dsimp [SATPhaseFlowState.energy, phaseFlowDissipationStep]
  exact phaseResidualEnergy_relax_nonincreasing sigma S.obstruction h0 h1

/-- THEOREM 7: with `0 < sigma < 1`, every state with positive residual
energy strictly dissipates. -/
theorem phaseFlowDissipationStep_energy_strict
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (h0 : 0 < sigma) (h1 : sigma < 1)
    (hE : 0 < S.energy) :
    (phaseFlowDissipationStep sigma dt direction S).energy < S.energy := by
  classical
  dsimp [SATPhaseFlowState.energy, phaseFlowDissipationStep] at hE ⊢
  exact phaseResidualEnergy_relax_strict sigma S.obstruction h0 h1 hE

/-! ## Certificate packaging -/

/-- P696 certificate: the P695 phase-flow surface has a certified residual
Lyapunov face whenever the runtime residual update is the saturation
consumption `r -> (1 - sigma) r`. -/
structure SATPhaseFlowLyapunovCertificate : Prop where
  p695_phase_surface :
    SATPhaseFlowSurfaceCertificate.{u, v}
  residual_energy_nonneg :
    ∀ {Clause : Type u} [Fintype Clause]
      (residual : Clause -> ℝ),
      0 <= phaseResidualEnergy residual
  residual_relax_energy_eq :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (residual : Clause -> ℝ),
      phaseResidualEnergy (phaseResidualRelaxStep sigma residual) =
        (1 - sigma) ^ 2 * phaseResidualEnergy residual
  residual_relax_energy_nonincreasing :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (residual : Clause -> ℝ),
      0 <= sigma -> sigma <= 1 ->
        phaseResidualEnergy (phaseResidualRelaxStep sigma residual) <=
          phaseResidualEnergy residual
  dissipative_step_energy_eq :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var),
      (phaseFlowDissipationStep sigma dt direction S).energy =
        (1 - sigma) ^ 2 * S.energy
  dissipative_step_energy_strict :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var),
      0 < sigma -> sigma < 1 -> 0 < S.energy ->
        (phaseFlowDissipationStep sigma dt direction S).energy < S.energy

/-- DEFINITION 1: canonical P696 Lyapunov certificate. -/
def satPhaseFlowLyapunovCertificate :
    SATPhaseFlowLyapunovCertificate.{u, v} where
  p695_phase_surface := satPhaseFlowSurfaceCertificate
  residual_energy_nonneg := by
    intro Clause _ residual
    exact phaseResidualEnergy_nonneg residual
  residual_relax_energy_eq := by
    intro Clause _ sigma residual
    exact phaseResidualEnergy_relax_eq sigma residual
  residual_relax_energy_nonincreasing := by
    intro Clause _ sigma residual h0 h1
    exact phaseResidualEnergy_relax_nonincreasing sigma residual h0 h1
  dissipative_step_energy_eq := by
    intro Clause Var _ sigma dt direction S
    exact phaseFlowDissipationStep_energy_eq sigma dt direction S
  dissipative_step_energy_strict := by
    intro Clause Var _ sigma dt direction S h0 h1 hE
    exact phaseFlowDissipationStep_energy_strict sigma dt direction S h0 h1 hE

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

/-- P696 grand root: P694/P695 plus a certified residual Lyapunov dissipation
face for the phase-flow surface. -/
structure PhaseFlowLyapunovUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p695_root :
    PhaseFlowSATUnifiedRootCertificate.{u, v, w, z} E0
  lyapunov_surface :
    SATPhaseFlowLyapunovCertificate.{v, w}

/-- THEOREM 8: the phase-flow Lyapunov unified root is inhabited. -/
def phaseFlowLyapunovUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    PhaseFlowLyapunovUnifiedRootCertificate.{u, v, w, z} E0 where
  p695_root := phaseFlowSATUnifiedRootCertificate (E0 := E0)
  lyapunov_surface := satPhaseFlowLyapunovCertificate

end GrandUnification

end SaturationMonoid
