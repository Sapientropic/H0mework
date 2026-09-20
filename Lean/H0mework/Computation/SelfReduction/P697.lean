import H0mework.Computation.SelfReduction.P696

/-!
# Proposition 697: iterated phase-residual dissipation

P696 proved the one-step Lyapunov law for the virtual-axis SAT phase-flow
surface:

`energy (r -> (1 - sigma) r) = (1 - sigma)^2 * energy r`.

This file pushes that certificate through finite iteration.  The result is the
exact geometric law

`energy_n = ((1 - sigma)^2)^n * energy_0`,

plus monotonicity and convergence to zero for `0 < sigma < 1`.

Boundary: this is still the certified residual reducer model.  It does not
prove that an arbitrary SAT implementation realizes this reducer, does not rule
out metastable chart-selection behavior outside the model, and does not prove a
polynomial SAT algorithm or `P = NP`.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

open Filter

open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Iterated residual relaxation -/

/-- `n` certified residual-relaxation steps at fixed saturation rate. -/
def phaseResidualRelaxIterate {Clause : Type*}
    (sigma : ℝ) : ℕ -> (Clause -> ℝ) -> Clause -> ℝ
  | 0, residual => residual
  | n + 1, residual =>
      phaseResidualRelaxStep sigma (phaseResidualRelaxIterate sigma n residual)

/-- THEOREM 1: zero residual-relaxation steps are the identity. -/
theorem phaseResidualRelaxIterate_zero {Clause : Type*}
    (sigma : ℝ) (residual : Clause -> ℝ) :
    phaseResidualRelaxIterate sigma 0 residual = residual := by
  rfl

/-- THEOREM 2: the closed-form residual after `n` steps is
`(1 - sigma)^n` times the initial residual. -/
theorem phaseResidualRelaxIterate_closed_form {Clause : Type*}
    (sigma : ℝ) (residual : Clause -> ℝ) :
    ∀ n : ℕ,
      phaseResidualRelaxIterate sigma n residual =
        fun c => (1 - sigma) ^ n * residual c := by
  intro n
  induction n with
  | zero =>
      ext c
      simp [phaseResidualRelaxIterate]
  | succ n ih =>
      ext c
      simp [phaseResidualRelaxIterate, phaseResidualRelaxStep, ih, pow_succ]
      ring_nf

/-- THEOREM 3: `n` residual-relaxation steps multiply squared energy by
`((1 - sigma)^2)^n`. -/
theorem phaseResidualEnergy_relax_iterate_eq
    {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (n : ℕ) (residual : Clause -> ℝ) :
    phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) =
      ((1 - sigma) ^ 2) ^ n * phaseResidualEnergy residual := by
  classical
  induction n with
  | zero =>
      simp [phaseResidualRelaxIterate]
  | succ n ih =>
      simp only [phaseResidualRelaxIterate]
      rw [phaseResidualEnergy_relax_eq, ih]
      rw [pow_succ]
      ring

/-- THEOREM 4: finite residual relaxation is Lyapunov nonincreasing whenever
`0 <= sigma <= 1`. -/
theorem phaseResidualEnergy_relax_iterate_nonincreasing
    {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (n : ℕ) (residual : Clause -> ℝ)
    (h0 : 0 <= sigma) (h1 : sigma <= 1) :
    phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) <=
      phaseResidualEnergy residual := by
  classical
  induction n with
  | zero =>
      simp [phaseResidualRelaxIterate]
  | succ n ih =>
      simp only [phaseResidualRelaxIterate]
      exact le_trans
        (phaseResidualEnergy_relax_nonincreasing sigma
          (phaseResidualRelaxIterate sigma n residual) h0 h1)
        ih

/-- THEOREM 5: for `0 < sigma < 1`, iterated residual-relaxation energy tends
to zero. -/
theorem tendsto_phaseResidualEnergy_relax_iterate_zero
    {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (residual : Clause -> ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1) :
    Tendsto (fun n : ℕ =>
      phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual))
      atTop (nhds (0 : ℝ)) := by
  classical
  have hbase_nonneg : 0 <= (1 - sigma) ^ 2 := by
    exact sq_nonneg (1 - sigma)
  have hbase_lt_one : (1 - sigma) ^ 2 < 1 := by
    nlinarith [sq_nonneg sigma, sq_nonneg (1 - sigma), h0, h1]
  have hpow :
      Tendsto (fun n : ℕ => ((1 - sigma) ^ 2) ^ n) atTop
        (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt_one
  have hclosed :
      (fun n : ℕ =>
        phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual)) =
        fun n : ℕ =>
          ((1 - sigma) ^ 2) ^ n * phaseResidualEnergy residual := by
    funext n
    exact phaseResidualEnergy_relax_iterate_eq sigma n residual
  rw [hclosed]
  simpa using hpow.mul tendsto_const_nhds

/-! ## Iterated dissipative phase-flow steps -/

/-- `n` certified dissipative phase-flow steps at fixed saturation rate, time
step, and direction field. -/
def phaseFlowDissipationIterate {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (n : ℕ)
    (S : SATPhaseFlowState Clause Var) :
    SATPhaseFlowState Clause Var :=
  match n with
  | 0 => S
  | k + 1 =>
      phaseFlowDissipationStep sigma dt direction
        (phaseFlowDissipationIterate sigma dt direction k S)

/-- THEOREM 6: `n` dissipative phase-flow steps multiply state energy by the
same geometric factor as the residual-only reducer. -/
theorem phaseFlowDissipationIterate_energy_eq
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (n : ℕ)
    (S : SATPhaseFlowState Clause Var) :
    (phaseFlowDissipationIterate sigma dt direction n S).energy =
      ((1 - sigma) ^ 2) ^ n * S.energy := by
  classical
  induction n with
  | zero =>
      simp [phaseFlowDissipationIterate]
  | succ n ih =>
      simp only [phaseFlowDissipationIterate]
      rw [phaseFlowDissipationStep_energy_eq, ih]
      rw [pow_succ]
      ring

/-- THEOREM 7: finite dissipative phase-flow iteration is Lyapunov
nonincreasing for runtime rates `0 <= sigma <= 1`. -/
theorem phaseFlowDissipationIterate_energy_nonincreasing
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (n : ℕ)
    (S : SATPhaseFlowState Clause Var)
    (h0 : 0 <= sigma) (h1 : sigma <= 1) :
    (phaseFlowDissipationIterate sigma dt direction n S).energy <= S.energy := by
  classical
  induction n with
  | zero =>
      simp [phaseFlowDissipationIterate]
  | succ n ih =>
      simp only [phaseFlowDissipationIterate]
      exact le_trans
        (phaseFlowDissipationStep_energy_nonincreasing sigma dt direction
          (phaseFlowDissipationIterate sigma dt direction n S) h0 h1)
        ih

/-- THEOREM 8: for `0 < sigma < 1`, iterated dissipative phase-flow energy
tends to zero. -/
theorem tendsto_phaseFlowDissipationIterate_energy_zero
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (h0 : 0 < sigma) (h1 : sigma < 1) :
    Tendsto (fun n : ℕ =>
      (phaseFlowDissipationIterate sigma dt direction n S).energy)
      atTop (nhds (0 : ℝ)) := by
  classical
  have hbase_nonneg : 0 <= (1 - sigma) ^ 2 := by
    exact sq_nonneg (1 - sigma)
  have hbase_lt_one : (1 - sigma) ^ 2 < 1 := by
    nlinarith [sq_nonneg sigma, sq_nonneg (1 - sigma), h0, h1]
  have hpow :
      Tendsto (fun n : ℕ => ((1 - sigma) ^ 2) ^ n) atTop
        (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt_one
  have hclosed :
      (fun n : ℕ =>
        (phaseFlowDissipationIterate sigma dt direction n S).energy) =
        fun n : ℕ => ((1 - sigma) ^ 2) ^ n * S.energy := by
    funext n
    exact phaseFlowDissipationIterate_energy_eq sigma dt direction n S
  rw [hclosed]
  simpa using hpow.mul tendsto_const_nhds

/-! ## Certificate packaging -/

/-- P697 certificate: the P696 one-step Lyapunov face iterates to an exact
geometric energy law and convergence to zero under positive subunit rate. -/
structure SATPhaseFlowIteratedLyapunovCertificate : Prop where
  p696_lyapunov :
    SATPhaseFlowLyapunovCertificate.{u, v}
  residual_iterate_closed_form :
    ∀ {Clause : Type u}
      (sigma : ℝ) (residual : Clause -> ℝ) (n : ℕ),
      phaseResidualRelaxIterate sigma n residual =
        fun c => (1 - sigma) ^ n * residual c
  residual_iterate_energy_eq :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (n : ℕ) (residual : Clause -> ℝ),
      phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) =
        ((1 - sigma) ^ 2) ^ n * phaseResidualEnergy residual
  residual_iterate_energy_tendsto_zero :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (residual : Clause -> ℝ),
      0 < sigma -> sigma < 1 ->
        Tendsto (fun n : ℕ =>
          phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual))
          atTop (nhds (0 : ℝ))
  dissipative_iterate_energy_eq :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (n : ℕ)
      (S : SATPhaseFlowState Clause Var),
      (phaseFlowDissipationIterate sigma dt direction n S).energy =
        ((1 - sigma) ^ 2) ^ n * S.energy
  dissipative_iterate_energy_tendsto_zero :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var),
      0 < sigma -> sigma < 1 ->
        Tendsto (fun n : ℕ =>
          (phaseFlowDissipationIterate sigma dt direction n S).energy)
          atTop (nhds (0 : ℝ))

/-- DEFINITION 1: canonical P697 iterated Lyapunov certificate. -/
def satPhaseFlowIteratedLyapunovCertificate :
    SATPhaseFlowIteratedLyapunovCertificate.{u, v} where
  p696_lyapunov := satPhaseFlowLyapunovCertificate
  residual_iterate_closed_form := by
    intro Clause sigma residual n
    exact phaseResidualRelaxIterate_closed_form sigma residual n
  residual_iterate_energy_eq := by
    intro Clause _ sigma n residual
    exact phaseResidualEnergy_relax_iterate_eq sigma n residual
  residual_iterate_energy_tendsto_zero := by
    intro Clause _ sigma residual h0 h1
    exact tendsto_phaseResidualEnergy_relax_iterate_zero sigma residual h0 h1
  dissipative_iterate_energy_eq := by
    intro Clause Var _ sigma dt direction n S
    exact phaseFlowDissipationIterate_energy_eq sigma dt direction n S
  dissipative_iterate_energy_tendsto_zero := by
    intro Clause Var _ sigma dt direction S h0 h1
    exact tendsto_phaseFlowDissipationIterate_energy_zero
      sigma dt direction S h0 h1

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

/-- P697 grand root: P696 plus finite-iterate and convergence laws for the
certified residual dissipation model. -/
structure PhaseFlowIteratedLyapunovUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p696_root :
    PhaseFlowLyapunovUnifiedRootCertificate.{u, v, w, z} E0
  iterated_lyapunov_surface :
    SATPhaseFlowIteratedLyapunovCertificate.{v, w}

/-- THEOREM 9: the phase-flow iterated Lyapunov unified root is inhabited. -/
def phaseFlowIteratedLyapunovUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    PhaseFlowIteratedLyapunovUnifiedRootCertificate.{u, v, w, z} E0 where
  p696_root := phaseFlowLyapunovUnifiedRootCertificate (E0 := E0)
  iterated_lyapunov_surface := satPhaseFlowIteratedLyapunovCertificate

end GrandUnification

end SaturationMonoid
