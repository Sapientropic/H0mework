/-
  Proposition 22: observable phase-kernel criterion.

  Lemma 3 covers contraction.  The critical `ρ = 1` boundary can leave a
  non-decaying phase residual instead of a pointwise difference that contracts
  away.  The full theorem "when does a reducer produce such a phase?" is a
  dynamical-systems problem.  This module proves the semantic half that the
  prose needs:

    if the residual phase lies in the observation kernel, then the two states
    (or two trajectories) remain observationally equal.

  In other words, phase holonomy is only an obstruction when it is visible to
  `obs`.
-/

import H0mework.Realization.Observation.Interference

/-- A phase action together with an observation map and its invisible kernel. -/
structure PhaseObservation (Phase State Obs : Type*) where
  act : Phase → State → State
  obs : State → Obs
  inObsKernel : Phase → Prop
  kernel_invisible : ∀ phase x, inObsKernel phase → obs (act phase x) = obs x

/-- THEOREM 1: a one-step phase residual in the observation kernel is invisible. -/
theorem phaseResidual_in_kernel_observable
    {Phase State Obs : Type*} (P : PhaseObservation Phase State Obs)
    {phase : Phase} (hphase : P.inObsKernel phase)
    {x y : State} (hy : y = P.act phase x) :
    P.obs y = P.obs x := by
  subst y
  exact P.kernel_invisible phase x hphase

/-- THEOREM 2: if every point of a trajectory differs by one invisible phase,
    the whole observed trajectory is pointwise equal. -/
theorem phaseResidual_trajectory_in_kernel_observable
    {Phase State Obs : Type*} (P : PhaseObservation Phase State Obs)
    {phase : Phase} (hphase : P.inObsKernel phase)
    {x y : Nat → State}
    (hy : ∀ n, y n = P.act phase (x n)) :
    ∀ n, P.obs (y n) = P.obs (x n) := by
  intro n
  exact phaseResidual_in_kernel_observable P hphase (hy n)

/-- THEOREM 3: visible phase residuals are the only possible phase-kernel
    obstruction for a paired state, in the sense that non-equal observations
    refute kernel membership. -/
theorem phaseResidual_observable_difference_not_in_kernel
    {Phase State Obs : Type*} (P : PhaseObservation Phase State Obs)
    {phase : Phase} {x y : State}
    (hy : y = P.act phase x)
    (hdiff : P.obs y ≠ P.obs x) :
    ¬ P.inObsKernel phase := by
  intro hphase
  exact hdiff (phaseResidual_in_kernel_observable P hphase hy)

/-!
  Summary:
  - A critical phase residual is semantically harmless exactly when the residual
    phase is invisible to observation.
  - Therefore a `ρ = 1` holonomy only becomes an observable obstruction after
    it leaves `ker(obs)`.

  Boundary:
  - This module does not prove that a concrete nonlinear reducer has a phase
    action, nor how to compute the residual phase.  It proves the observation
    criterion once such a phase certificate is supplied.
-/
