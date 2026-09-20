import H0mework.Computation.SelfReduction.P698

/-!
# Proposition 699: epsilon threshold certificates for residual dissipation

P697 gives convergence of the certified residual reducer.  P698 identifies the
zero-energy target with obstruction freedom.  This file extracts the runtime
threshold form:

for every positive energy threshold `ε`, there is a finite index after which
the certified reducer stays below `ε`; and an energy threshold controls every
individual clause residual.

Boundary: this is an eventual threshold certificate, not a finite-time exact
zero theorem.  For `0 < sigma < 1`, the certified reducer generally converges
geometrically to zero; it is not claimed to hit zero in finitely many steps
unless the initial residual is already zero or a runtime threshold gate chooses
to collapse it.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

open Filter

open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Eventual energy thresholds -/

/-- THEOREM 1: for every positive threshold, residual-relaxation energy is
eventually below it. -/
theorem eventually_phaseResidualEnergy_relax_iterate_lt
    {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (residual : Clause -> ℝ)
    (epsilon : ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1) (hε : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) <
        epsilon := by
  classical
  have htend :=
    tendsto_phaseResidualEnergy_relax_iterate_zero sigma residual h0 h1
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) <
          epsilon :=
    htend.eventually (isOpen_Iio.mem_nhds hε)
  exact eventually_atTop.mp hevent

/-- THEOREM 2: for every positive threshold, full dissipative phase-flow energy
is eventually below it. -/
theorem eventually_phaseFlowDissipationIterate_energy_lt
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (epsilon : ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1) (hε : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      (phaseFlowDissipationIterate sigma dt direction n S).energy <
        epsilon := by
  classical
  have htend :=
    tendsto_phaseFlowDissipationIterate_energy_zero
      sigma dt direction S h0 h1
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (phaseFlowDissipationIterate sigma dt direction n S).energy <
          epsilon :=
    htend.eventually (isOpen_Iio.mem_nhds hε)
  exact eventually_atTop.mp hevent

/-! ## Energy threshold controls pointwise residuals -/

/-- THEOREM 3: if total residual energy is below `epsilon`, every squared
clause residual is below `epsilon`. -/
theorem residual_sq_lt_of_phaseResidualEnergy_lt
    {Clause : Type*} [Fintype Clause]
    (residual : Clause -> ℝ) {epsilon : ℝ}
    (hE : phaseResidualEnergy residual < epsilon)
    (c : Clause) :
    (residual c) ^ 2 < epsilon := by
  classical
  have hterm_le :
      (residual c) ^ 2 <= phaseResidualEnergy residual := by
    dsimp [phaseResidualEnergy]
    exact Finset.single_le_sum
      (fun x _ => sq_nonneg (residual x))
      (Finset.mem_univ c)
  exact lt_of_le_of_lt hterm_le hE

/-- THEOREM 4: if total residual energy is below `delta^2`, every clause
residual has absolute value below `delta`. -/
theorem abs_residual_lt_of_phaseResidualEnergy_lt_sq
    {Clause : Type*} [Fintype Clause]
    (residual : Clause -> ℝ) {delta : ℝ}
    (hδ : 0 < delta)
    (hE : phaseResidualEnergy residual < delta ^ 2)
    (c : Clause) :
    |residual c| < delta := by
  classical
  have hsq : (residual c) ^ 2 < delta ^ 2 :=
    residual_sq_lt_of_phaseResidualEnergy_lt residual hE c
  have hsq_abs : |residual c| ^ 2 < delta ^ 2 := by
    simpa [sq_abs] using hsq
  by_contra hnot
  have hle : delta <= |residual c| := le_of_not_gt hnot
  have habs_nonneg : 0 <= |residual c| := abs_nonneg (residual c)
  have hsq_ge : delta ^ 2 <= |residual c| ^ 2 := by
    nlinarith
  nlinarith

/-- THEOREM 5: after enough certified residual-relaxation steps, every clause
residual is below a chosen absolute threshold. -/
theorem eventually_abs_phaseResidualRelaxIterate_lt
    {Clause : Type*} [Fintype Clause]
    (sigma : ℝ) (residual : Clause -> ℝ)
    (delta : ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1) (hδ : 0 < delta) :
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      ∀ c : Clause, |phaseResidualRelaxIterate sigma n residual c| < delta := by
  classical
  have hδsq : 0 < delta ^ 2 := by
    nlinarith
  rcases eventually_phaseResidualEnergy_relax_iterate_lt
      sigma residual (delta ^ 2) h0 h1 hδsq with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn c
  exact abs_residual_lt_of_phaseResidualEnergy_lt_sq
    (phaseResidualRelaxIterate sigma n residual) hδ (hN n hn) c

/-- THEOREM 6: after enough certified dissipative phase-flow steps, every
obstruction residual in the state is below a chosen absolute threshold. -/
theorem eventually_abs_phaseFlowDissipationIterate_obstruction_lt
    {Clause Var : Type*} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : SATPhaseFlowState Clause Var)
    (delta : ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1) (hδ : 0 < delta) :
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      ∀ c : Clause,
        |(phaseFlowDissipationIterate sigma dt direction n S).obstruction c|
          < delta := by
  classical
  have hδsq : 0 < delta ^ 2 := by
    nlinarith
  rcases eventually_phaseFlowDissipationIterate_energy_lt
      sigma dt direction S (delta ^ 2) h0 h1 hδsq with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn c
  have hE :
      phaseResidualEnergy
          (phaseFlowDissipationIterate sigma dt direction n S).obstruction
        < delta ^ 2 := by
    simpa [SATPhaseFlowState.energy] using hN n hn
  exact abs_residual_lt_of_phaseResidualEnergy_lt_sq
    (phaseFlowDissipationIterate sigma dt direction n S).obstruction hδ hE c

/-! ## Certificate packaging -/

/-- P699 certificate: the certified residual reducer supplies finite threshold
entry indices and pointwise residual bounds. -/
structure SATPhaseFlowEpsilonThresholdCertificate : Prop where
  p698_energy_zero :
    SATPhaseFlowEnergyZeroObstructionCertificate.{u, v}
  residual_energy_eventually_below :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (residual : Clause -> ℝ) (epsilon : ℝ),
      0 < sigma -> sigma < 1 -> 0 < epsilon ->
        ∃ N : ℕ, ∀ n : ℕ, N <= n ->
          phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) <
            epsilon
  phase_energy_eventually_below :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var)
      (epsilon : ℝ),
      0 < sigma -> sigma < 1 -> 0 < epsilon ->
        ∃ N : ℕ, ∀ n : ℕ, N <= n ->
          (phaseFlowDissipationIterate sigma dt direction n S).energy <
            epsilon
  residual_pointwise_threshold :
    ∀ {Clause : Type u} [Fintype Clause]
      (residual : Clause -> ℝ) {delta : ℝ},
      0 < delta -> phaseResidualEnergy residual < delta ^ 2 ->
        ∀ c : Clause, |residual c| < delta
  residual_iterate_pointwise_eventually_below :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (residual : Clause -> ℝ) (delta : ℝ),
      0 < sigma -> sigma < 1 -> 0 < delta ->
        ∃ N : ℕ, ∀ n : ℕ, N <= n ->
          ∀ c : Clause, |phaseResidualRelaxIterate sigma n residual c| < delta
  phase_iterate_obstruction_eventually_below :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : SATPhaseFlowState Clause Var)
      (delta : ℝ),
      0 < sigma -> sigma < 1 -> 0 < delta ->
        ∃ N : ℕ, ∀ n : ℕ, N <= n ->
          ∀ c : Clause,
            |(phaseFlowDissipationIterate sigma dt direction n S).obstruction c|
              < delta

/-- DEFINITION 1: canonical P699 epsilon-threshold certificate. -/
def satPhaseFlowEpsilonThresholdCertificate :
    SATPhaseFlowEpsilonThresholdCertificate.{u, v} where
  p698_energy_zero := satPhaseFlowEnergyZeroObstructionCertificate
  residual_energy_eventually_below := by
    intro Clause _ sigma residual epsilon h0 h1 hε
    exact eventually_phaseResidualEnergy_relax_iterate_lt
      sigma residual epsilon h0 h1 hε
  phase_energy_eventually_below := by
    intro Clause Var _ sigma dt direction S epsilon h0 h1 hε
    exact eventually_phaseFlowDissipationIterate_energy_lt
      sigma dt direction S epsilon h0 h1 hε
  residual_pointwise_threshold := by
    intro Clause _ residual delta hδ hE c
    exact abs_residual_lt_of_phaseResidualEnergy_lt_sq residual hδ hE c
  residual_iterate_pointwise_eventually_below := by
    intro Clause _ sigma residual delta h0 h1 hδ
    exact eventually_abs_phaseResidualRelaxIterate_lt
      sigma residual delta h0 h1 hδ
  phase_iterate_obstruction_eventually_below := by
    intro Clause Var _ sigma dt direction S delta h0 h1 hδ
    exact eventually_abs_phaseFlowDissipationIterate_obstruction_lt
      sigma dt direction S delta h0 h1 hδ

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

/-- P699 grand root: P698 plus finite threshold-entry certificates for the
certified residual reducer. -/
structure PhaseFlowEpsilonThresholdUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p698_root :
    PhaseFlowEnergyZeroObstructionUnifiedRootCertificate.{u, v, w, z} E0
  epsilon_threshold_surface :
    SATPhaseFlowEpsilonThresholdCertificate.{v, w}

/-- THEOREM 7: the phase-flow epsilon-threshold unified root is inhabited. -/
def phaseFlowEpsilonThresholdUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    PhaseFlowEpsilonThresholdUnifiedRootCertificate.{u, v, w, z} E0 where
  p698_root := phaseFlowEnergyZeroObstructionUnifiedRootCertificate (E0 := E0)
  epsilon_threshold_surface := satPhaseFlowEpsilonThresholdCertificate

end GrandUnification

end SaturationMonoid
