import H0mework.Computation.SelfReduction.P697

/-!
# Proposition 698: zero energy is exactly obstruction freedom

P697 proved that the certified residual reducer dissipates squared residual
energy geometrically.  This file connects that Lyapunov scalar back to the
P695 phase-obstruction semantics.

For a finite clause surface,

`sum_c r_c^2 = 0`

is equivalent to `r_c = 0` for every clause.  Therefore zero Lyapunov energy is
not merely a numerical convention: it is exactly the obstruction-free surface
on which P695's phase-flow step is fixed.

Boundary: this proves the semantic zero set of the certified residual energy.
It does not prove that arbitrary CNF dynamics reaches that zero set in finite
time, nor that every runtime reducer is the certified saturation reducer, nor
`P = NP`.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Energy zero iff every residual is zero -/

/-- THEOREM 1: zero squared residual energy is exactly pointwise zero
residual. -/
theorem phaseResidualEnergy_eq_zero_iff
    {Clause : Type*} [Fintype Clause]
    (residual : Clause -> ℝ) :
    phaseResidualEnergy residual = 0 ↔ ∀ c, residual c = 0 := by
  classical
  constructor
  · intro hE c
    have hterm_le :
        (residual c) ^ 2 <= phaseResidualEnergy residual := by
      dsimp [phaseResidualEnergy]
      exact Finset.single_le_sum
        (fun x _ => sq_nonneg (residual x))
        (Finset.mem_univ c)
    have hterm_nonpos : (residual c) ^ 2 <= 0 := by
      simpa [hE] using hterm_le
    have hterm_zero : (residual c) ^ 2 = 0 :=
      le_antisymm hterm_nonpos (sq_nonneg (residual c))
    nlinarith
  · intro hzero
    dsimp [phaseResidualEnergy]
    simp [hzero]

/-- THEOREM 2: positive residual at any clause forces positive energy. -/
theorem phaseResidualEnergy_pos_of_residual_ne_zero
    {Clause : Type*} [Fintype Clause]
    (residual : Clause -> ℝ) {c : Clause}
    (hc : residual c ≠ 0) :
    0 < phaseResidualEnergy residual := by
  classical
  have hnot : phaseResidualEnergy residual ≠ 0 := by
    intro hE
    have hzero := (phaseResidualEnergy_eq_zero_iff residual).mp hE
    exact hc (hzero c)
  have hnonneg := phaseResidualEnergy_nonneg residual
  exact lt_of_le_of_ne' hnonneg hnot

/-! ## Zero energy freezes the phase-flow surface -/

/-- THEOREM 3: zero residual energy gives P695's no-motion theorem for the
raw phase step. -/
theorem phaseFlowStep_fixed_of_energy_zero
    {Clause Var : Type*} [Fintype Clause]
    (theta : Var -> ℝ)
    (obstruction : Clause -> ℝ)
    (direction : Clause -> Var -> ℝ)
    (dt : ℝ) (i : Var)
    (hE : phaseResidualEnergy obstruction = 0) :
    phaseFlowStep theta obstruction direction dt i = theta i := by
  classical
  have hzero : ∀ c, obstruction c = 0 :=
    (phaseResidualEnergy_eq_zero_iff obstruction).mp hE
  exact phaseFlowStep_fixed_of_all_obstruction_zero
    theta obstruction direction dt i hzero

/-- THEOREM 4: zero state energy fixes the angle component of one certified
dissipative phase step. -/
theorem phaseFlowDissipationStep_theta_fixed_of_energy_zero
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (hE : S.energy = 0) :
    (phaseFlowDissipationStep sigma dt direction S).theta = S.theta := by
  classical
  funext i
  dsimp [phaseFlowDissipationStep]
  have hE' : phaseResidualEnergy S.obstruction = 0 := by
    simpa [SATPhaseFlowState.energy] using hE
  exact phaseFlowStep_fixed_of_energy_zero
    S.theta S.obstruction direction dt i hE'

/-- THEOREM 5: zero state energy fixes the whole certified dissipative phase
step: angles do not move, and zero residuals remain zero after saturation. -/
theorem phaseFlowDissipationStep_fixed_of_energy_zero
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (hE : S.energy = 0) :
    phaseFlowDissipationStep sigma dt direction S = S := by
  classical
  cases S with
  | mk theta obstruction =>
      have hE' : phaseResidualEnergy obstruction = 0 := by
        simpa [SATPhaseFlowState.energy] using hE
      have hzero : ∀ c, obstruction c = 0 :=
        (phaseResidualEnergy_eq_zero_iff obstruction).mp hE'
      have htheta :
          phaseFlowStep theta obstruction direction dt = theta := by
        funext i
        exact phaseFlowStep_fixed_of_all_obstruction_zero
          theta obstruction direction dt i hzero
      have hobstruction :
          phaseResidualRelaxStep sigma obstruction = obstruction := by
        funext c
        dsimp [phaseResidualRelaxStep]
        simp [hzero c]
      change
        SATPhaseFlowState.mk
          (phaseFlowStep theta obstruction direction dt)
          (phaseResidualRelaxStep sigma obstruction) =
        SATPhaseFlowState.mk theta obstruction
      rw [htheta, hobstruction]

/-- THEOREM 6: if the initial state has zero energy, every certified
dissipative iterate leaves it exactly fixed. -/
theorem phaseFlowDissipationIterate_fixed_of_energy_zero
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (n : ℕ)
    (S : SATPhaseFlowState Clause Var)
    (hE : S.energy = 0) :
    phaseFlowDissipationIterate sigma dt direction n S = S := by
  classical
  induction n with
  | zero =>
      simp [phaseFlowDissipationIterate]
  | succ n ih =>
      simp only [phaseFlowDissipationIterate]
      rw [ih]
      exact phaseFlowDissipationStep_fixed_of_energy_zero
        sigma dt direction S hE

/-! ## Certificate packaging -/

/-- P698 certificate: the Lyapunov energy zero set is exactly the
obstruction-free phase surface, and certified dissipative phase-flow fixes that
surface. -/
structure SATPhaseFlowEnergyZeroObstructionCertificate : Prop where
  p697_iterated_lyapunov :
    SATPhaseFlowIteratedLyapunovCertificate.{u, v}
  energy_zero_iff_obstruction_free :
    ∀ {Clause : Type u} [Fintype Clause]
      (residual : Clause -> ℝ),
      phaseResidualEnergy residual = 0 ↔ ∀ c, residual c = 0
  positive_residual_forces_positive_energy :
    ∀ {Clause : Type u} [Fintype Clause]
      (residual : Clause -> ℝ) {c : Clause},
      residual c ≠ 0 -> 0 < phaseResidualEnergy residual
  energy_zero_phase_step_fixed :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (theta : Var -> ℝ)
      (obstruction : Clause -> ℝ)
      (direction : Clause -> Var -> ℝ)
      (dt : ℝ) (i : Var),
      phaseResidualEnergy obstruction = 0 ->
        phaseFlowStep theta obstruction direction dt i = theta i
  energy_zero_dissipation_step_fixed :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var),
      S.energy = 0 ->
        phaseFlowDissipationStep sigma dt direction S = S
  energy_zero_dissipation_iterate_fixed :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (n : ℕ)
      (S : SATPhaseFlowState Clause Var),
      S.energy = 0 ->
        phaseFlowDissipationIterate sigma dt direction n S = S

/-- DEFINITION 1: canonical P698 energy-zero obstruction certificate. -/
def satPhaseFlowEnergyZeroObstructionCertificate :
    SATPhaseFlowEnergyZeroObstructionCertificate.{u, v} where
  p697_iterated_lyapunov := satPhaseFlowIteratedLyapunovCertificate
  energy_zero_iff_obstruction_free := by
    intro Clause _ residual
    exact phaseResidualEnergy_eq_zero_iff residual
  positive_residual_forces_positive_energy := by
    intro Clause _ residual c hc
    exact phaseResidualEnergy_pos_of_residual_ne_zero residual hc
  energy_zero_phase_step_fixed := by
    intro Clause Var _ theta obstruction direction dt i hE
    exact phaseFlowStep_fixed_of_energy_zero
      theta obstruction direction dt i hE
  energy_zero_dissipation_step_fixed := by
    intro Clause Var _ sigma dt direction S hE
    exact phaseFlowDissipationStep_fixed_of_energy_zero
      sigma dt direction S hE
  energy_zero_dissipation_iterate_fixed := by
    intro Clause Var _ sigma dt direction n S hE
    exact phaseFlowDissipationIterate_fixed_of_energy_zero
      sigma dt direction n S hE

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

/-- P698 grand root: P697 plus the zero-energy = obstruction-free semantic
bridge back to P695 phase no-motion. -/
structure PhaseFlowEnergyZeroObstructionUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p697_root :
    PhaseFlowIteratedLyapunovUnifiedRootCertificate.{u, v, w, z} E0
  energy_zero_obstruction_surface :
    SATPhaseFlowEnergyZeroObstructionCertificate.{v, w}

/-- THEOREM 7: the phase-flow energy-zero obstruction unified root is
inhabited. -/
def phaseFlowEnergyZeroObstructionUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    PhaseFlowEnergyZeroObstructionUnifiedRootCertificate.{u, v, w, z} E0 where
  p697_root := phaseFlowIteratedLyapunovUnifiedRootCertificate (E0 := E0)
  energy_zero_obstruction_surface :=
    satPhaseFlowEnergyZeroObstructionCertificate

end GrandUnification

end SaturationMonoid
