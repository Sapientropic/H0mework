import H0mework.Physics.GravitySource.ResidualOrbitConnectionLift
import H0mework.Physics.MatterJets.SourceMatterFirstJetResidualOrbit

/-!
# S9-C3h17: residual-limit and matter-orbit joint lift classification

This module combines two already generated readouts without inventing another
carrier.  The residual-limit six-field class closes all three algebraic origin
coordinates.  Consecutive realizers of the source matter first-jet orbit close
the complete conjugate-matter coordinate of the physical lift defect.

Consequently an actual update between endpoints satisfying both conditions
has exactly five still-open origin coordinates: Lorentz connection, P286 gauge
connection, scalar, matter, and coframe.  Full `D_U = 0` is equivalent to
those five coordinates vanishing.

Both endpoint conditions and the update remain explicit readout hypotheses.
This classification generates no configuration, germ, update, zero-fiber
witness, or stationarity receipt.
-/

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitMatterOrbitJointClassification

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineJointStateLiftDefect
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineSourceMatterFirstJetResidualOrbit

noncomputable section

set_option autoImplicit false

/-- Reader class combining only the already generated residual-limit partial
carrier and one transported matter first jet. -/
structure ExtendsResidualLimitAndMatterOrbitAt
    (n : ℕ) (configuration : StageNineHolonomicConfiguration) : Prop where
  residualLimit :
    ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration
  matterOrbit :
    RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration

theorem consecutiveResidualLimitMatterOrbit_liftDefect_algebraic_eq_zero
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends : ExtendsResidualLimitAndMatterOrbitAt n initial)
    (terminalExtends : ExtendsResidualLimitAndMatterOrbitAt (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial) 0).algebraic = 0 := by
  apply CurrentPointwiseAlgebraicResidualCarrier.ext
  · change
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          (update initial) 0).gravitySimplicity -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            initial 0).gravitySimplicity = 0
    rw [updateInitial,
      residualLimitExtension_gravitySimplicityResidual_origin
        terminal terminalExtends.residualLimit,
      residualLimitExtension_gravitySimplicityResidual_origin
        initial initialExtends.residualLimit]
    simp
  · change
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          (update initial) 0).gravityAuxiliary -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            initial 0).gravityAuxiliary = 0
    rw [updateInitial,
      residualLimitExtension_gravityAuxiliaryResidual_origin
        terminal terminalExtends.residualLimit,
      residualLimitExtension_gravityAuxiliaryResidual_origin
        initial initialExtends.residualLimit]
    simp
  · change
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          (update initial) 0).p286GaugeAuxiliary -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            initial 0).p286GaugeAuxiliary = 0
    rw [updateInitial,
      residualLimitExtension_p286GaugeAuxiliaryResidual_origin
        terminal terminalExtends.residualLimit,
      residualLimitExtension_p286GaugeAuxiliaryResidual_origin
        initial initialExtends.residualLimit]
    simp

theorem consecutiveResidualLimitMatterOrbit_liftDefect_conjugateMatter_eq_zero
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends : ExtendsResidualLimitAndMatterOrbitAt n initial)
    (terminalExtends : ExtendsResidualLimitAndMatterOrbitAt (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial) 0).eulerLagrange.conjugateMatter = 0 :=
  realizingOrbit_conjugateLiftDefect_eq_zero_allDirections n
    initial terminal initialExtends.matterOrbit terminalExtends.matterOrbit
    update updateInitial

/-- Exact remaining pointwise responsibility: after the four already closed
coordinates, full lift closure is equivalent to the other five EL channels. -/
theorem consecutiveResidualLimitMatterOrbit_liftDefect_eq_zero_iff_five
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends : ExtendsResidualLimitAndMatterOrbitAt n initial)
    (terminalExtends : ExtendsResidualLimitAndMatterOrbitAt (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    (currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial) 0 = 0 ↔
      ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
          initial) 0).eulerLagrange.lorentzConnection = 0 ∧
      ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
          initial) 0).eulerLagrange.p286GaugeConnection = 0 ∧
      ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
          initial) 0).eulerLagrange.scalar = 0 ∧
      ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
          initial) 0).eulerLagrange.matter = 0 ∧
      ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
          initial) 0).eulerLagrange.coframe = 0 := by
  let defect :=
    (currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
      initial) 0
  have algebraicZero : defect.algebraic = 0 :=
    consecutiveResidualLimitMatterOrbit_liftDefect_algebraic_eq_zero n
      initial terminal initialExtends terminalExtends update updateInitial
  have conjugateZero : defect.eulerLagrange.conjugateMatter = 0 :=
    consecutiveResidualLimitMatterOrbit_liftDefect_conjugateMatter_eq_zero n
      initial terminal initialExtends terminalExtends update updateInitial
  constructor
  · intro defectZero
    have eulerZero : defect.eulerLagrange = 0 := congrArg
      CurrentPointwiseJointShellResidualCarrier.eulerLagrange defectZero
    exact ⟨congrArg CurrentPointwiseEulerLagrangeResidualCarrier.lorentzConnection
        eulerZero,
      congrArg CurrentPointwiseEulerLagrangeResidualCarrier.p286GaugeConnection
        eulerZero,
      congrArg CurrentPointwiseEulerLagrangeResidualCarrier.scalar eulerZero,
      congrArg CurrentPointwiseEulerLagrangeResidualCarrier.matter eulerZero,
      congrArg CurrentPointwiseEulerLagrangeResidualCarrier.coframe eulerZero⟩
  · rintro ⟨lorentzZero, p286Zero, scalarZero, matterZero, coframeZero⟩
    apply CurrentPointwiseJointShellResidualCarrier.ext
    · exact algebraicZero
    · apply CurrentPointwiseEulerLagrangeResidualCarrier.ext
      · exact lorentzZero
      · exact p286Zero
      · exact scalarZero
      · exact matterZero
      · exact conjugateZero
      · exact coframeZero

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitMatterOrbitJointClassification
