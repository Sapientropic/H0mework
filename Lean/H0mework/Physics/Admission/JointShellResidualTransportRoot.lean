import H0mework.Physics.Geometry.JointShellZeroFiber
import H0mework.Realization.Residual.Process
import H0mework.Realization.Residual.Algebra
import Mathlib.Algebra.Module.TransferInstance

/-!
# S9-C3h2: joint-shell residual transport root

This module reconnects the complete current nine-channel Stage-9 residual to
the framework's first formula before any further configuration repair:

`r' = K r`, `r = K r + (I-K)r`, and `trace = (I-K)r`.

The current joint residual carrier first receives only its canonical
componentwise real-module structure.  The same proof-free source's existing
`sigma` then generates the scalar keep `K`; no new coefficient, branch choice,
trace slot, shell witness, or stationarity receipt is introduced.  The action
and holonomic configuration enter only through the downstream residual readout
`currentJointShellResidualSection`.

The complete residual section itself is then registered as an
`EffectiveResidualProcess`: its state is `r`, its update is `K r`, and its
residual readout is the identity.  This is the domain-native carrier process
that a later physical configuration update must lift; it is not a supplied
configuration witness.

The forced trace is unique.  Since the source-generated keep is active, the
global joint-shell zero fiber is exactly the zero fiber of that trace, hence
exactly the already classified nine strong equations.  Consequently a
nonzero current residual cannot be hidden in a zero/naked third sink.

This is a Layer-0/Layer-1 checkpoint.  It does not prove source reachability of
the zero fiber, construct a configuration, or authorize a new repair field.
-/

namespace SaturationMonoid.PhysicsCore.StageNineJointShellResidualTransportRoot

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineJointShellResidualCarrier
open StageNineJointShellZeroFiber
open ResidualProjection

noncomputable section

set_option autoImplicit false

/-! ## Canonical linear carrier -/

abbrev CurrentPointwiseAlgebraicResidualCoordinates :=
  PhysicalBivector × PhysicalBivector × P286GaugeTwoForm

abbrev CurrentPointwiseEulerLagrangeResidualCoordinates :=
  (LorentzBivectorOneForm → ℝ) ×
    (P286GaugeOneForm → ℝ) ×
      (ScalarCoordinateCarrier → ℝ) ×
        (MatterCoordinateCarrier → ℝ) ×
          (MatterCoordinateCarrier → ℝ) ×
            (LorentzianCoframe →L[ℝ] ℝ)

abbrev CurrentPointwiseJointShellResidualCoordinates :=
  CurrentPointwiseAlgebraicResidualCoordinates ×
    CurrentPointwiseEulerLagrangeResidualCoordinates

/-- Coordinate equivalence exposing exactly the nine existing residual
channels.  It adds no new coordinate and forgets none. -/
def currentPointwiseJointShellResidualCoordinateEquiv :
    CurrentPointwiseJointShellResidualCarrier ≃
      CurrentPointwiseJointShellResidualCoordinates where
  toFun residual :=
    ((residual.algebraic.gravitySimplicity,
        residual.algebraic.gravityAuxiliary,
        residual.algebraic.p286GaugeAuxiliary),
      (residual.eulerLagrange.lorentzConnection,
        residual.eulerLagrange.p286GaugeConnection,
        residual.eulerLagrange.scalar,
        residual.eulerLagrange.matter,
        residual.eulerLagrange.conjugateMatter,
        residual.eulerLagrange.coframe))
  invFun coordinates :=
    { algebraic :=
        { gravitySimplicity := coordinates.1.1
          gravityAuxiliary := coordinates.1.2.1
          p286GaugeAuxiliary := coordinates.1.2.2 }
      eulerLagrange :=
        { lorentzConnection := coordinates.2.1
          p286GaugeConnection := coordinates.2.2.1
          scalar := coordinates.2.2.2.1
          matter := coordinates.2.2.2.2.1
          conjugateMatter := coordinates.2.2.2.2.2.1
          coframe := coordinates.2.2.2.2.2.2 } }
  left_inv residual := by
    cases residual
    rfl
  right_inv coordinates := by
    rcases coordinates with
      ⟨⟨gravitySimplicity, gravityAuxiliary, p286GaugeAuxiliary⟩,
        lorentzConnection, p286GaugeConnection, scalar, matter,
        conjugateMatter, coframe⟩
    rfl

/-- The current joint carrier's additive structure is the transported
componentwise structure on its exact nine coordinates. -/
instance currentPointwiseJointShellResidualAddCommGroup :
    AddCommGroup CurrentPointwiseJointShellResidualCarrier :=
  currentPointwiseJointShellResidualCoordinateEquiv.addCommGroup

/-- The current joint carrier's scalar action is componentwise real scaling. -/
instance currentPointwiseJointShellResidualModule :
    Module ℝ CurrentPointwiseJointShellResidualCarrier :=
  currentPointwiseJointShellResidualCoordinateEquiv.module ℝ

abbrev CurrentJointShellResidualSection :=
  BasePoint → CurrentPointwiseJointShellResidualCarrier

/-! ## The source-generated keep and the first formula -/

/-- The complete joint residual keep `K`, generated by the same source sigma.
The holonomic configuration is deliberately absent from its arguments. -/
def currentJointShellResidualKeep
    (source : CurrentSmoothUnifiedSource) :
    CurrentJointShellResidualSection →ₗ[ℝ]
      CurrentJointShellResidualSection :=
  scalarKeepLinearMap source.legacy.sigma

/-- The framework's first formula as a genuine process on the complete
nine-channel residual carrier.  No physical configuration or zero-fiber
witness is stored here: the native state is the residual section itself,
`update r = K r`, and `residual r = r`. -/
def currentJointShellResidualEffectiveProcess
    (source : CurrentSmoothUnifiedSource) :
    EffectiveResidualProcess ℝ CurrentJointShellResidualSection
      CurrentJointShellResidualSection where
  target := 0
  keep := currentJointShellResidualKeep source
  residual := id
  update := currentJointShellResidualKeep source
  residual_transport_law := fun _ => rfl

@[simp] theorem currentJointShellResidualEffectiveProcess_residual
    (source : CurrentSmoothUnifiedSource)
    (residual : CurrentJointShellResidualSection) :
    (currentJointShellResidualEffectiveProcess source).residual residual =
      residual :=
  rfl

@[simp] theorem currentJointShellResidualEffectiveProcess_update
    (source : CurrentSmoothUnifiedSource)
    (residual : CurrentJointShellResidualSection) :
    (currentJointShellResidualEffectiveProcess source).update residual =
      currentJointShellResidualKeep source residual :=
  rfl

/-- Literal full-carrier process law `r' = K r`. -/
theorem currentJointShellResidualEffectiveProcess_transport
    (source : CurrentSmoothUnifiedSource)
    (residual : CurrentJointShellResidualSection) :
    (currentJointShellResidualEffectiveProcess source).residual
        ((currentJointShellResidualEffectiveProcess source).update residual) =
      currentJointShellResidualKeep source residual :=
  (currentJointShellResidualEffectiveProcess source).residual_transport_law
    residual

/-- First residual step `r' = K r` on the complete generated residual
section. -/
def transportedCurrentJointShellResidualSection
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellResidualSection :=
  currentJointShellResidualKeep source
    (currentJointShellResidualSection source configuration)

/-- The complementary responsibility is definitionally `(I-K)r`, never an
independent source or configuration field. -/
def currentJointShellResidualTrace
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellResidualSection :=
  linearResidualTrace (currentJointShellResidualKeep source)
    (currentJointShellResidualSection source configuration)

theorem transportedCurrentJointShellResidualSection_eq_keep
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    transportedCurrentJointShellResidualSection source configuration =
      currentJointShellResidualKeep source
        (currentJointShellResidualSection source configuration) :=
  rfl

/-- Literal operator form `trace = (I-K)r = r-Kr`. -/
theorem currentJointShellResidualTrace_eq_id_sub_keep
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    currentJointShellResidualTrace source configuration =
      currentJointShellResidualSection source configuration -
        currentJointShellResidualKeep source
          (currentJointShellResidualSection source configuration) :=
  rfl

theorem currentJointShellResidualTrace_eq_scalarTrace
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    currentJointShellResidualTrace source configuration =
      source.legacy.sigma •
        currentJointShellResidualSection source configuration := by
  exact residualTransportCore_scalar_trace source.legacy.sigma
    (currentJointShellResidualSection source configuration)

/-- Framework root on the actual complete current residual:
`r = K r + (I-K)r`. -/
theorem currentJointShellResidual_split
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    currentJointShellResidualSection source configuration =
      transportedCurrentJointShellResidualSection source configuration +
        currentJointShellResidualTrace source configuration :=
  residualTransportCore_residual_split
    (currentJointShellResidualKeep source)
    (currentJointShellResidualSection source configuration)

/-- Any complement satisfying the split is forced to be `(I-K)r`. -/
theorem currentJointShellResidualTrace_unique
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (trace : CurrentJointShellResidualSection) :
    currentJointShellResidualSection source configuration =
        transportedCurrentJointShellResidualSection source configuration +
          trace ↔
      trace = currentJointShellResidualTrace source configuration :=
  residualTransportCore_trace_unique
    (currentJointShellResidualKeep source)
    (currentJointShellResidualSection source configuration) trace

/-! ## Active transport, zero fiber, and no third sink -/

theorem currentJointShellResidualKeep_active
    (source : CurrentSmoothUnifiedSource) :
    ResidualTransportActive (currentJointShellResidualKeep source) := by
  exact scalarKeepLinearMap_active_of_ne_zero source.legacy.sigma
    (ne_of_gt source.legacy.sigma_pos)

/-- Negative regression: on an active source, a nonzero residual cannot use
the identity/no-op as its next state.  The only legitimate carrier successor
is the genuinely changed state `K r`. -/
theorem currentJointShellResidualEffectiveProcess_update_ne_self_of_ne_zero
    (source : CurrentSmoothUnifiedSource)
    (residual : CurrentJointShellResidualSection)
    (residual_ne_zero : residual ≠ 0) :
    (currentJointShellResidualEffectiveProcess source).update residual ≠
      residual := by
  intro noChange
  apply residual_ne_zero
  apply currentJointShellResidualKeep_active source residual
  simpa only [currentJointShellResidualEffectiveProcess_update] using noChange

/-- The global joint-shell zero fiber is exactly the zero forced-trace fiber.
This is a consequence of faithful transport, not a stored equation Boolean. -/
theorem currentJointShellZeroFiber_iff_trace_zero
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellZeroFiber source configuration ↔
      currentJointShellResidualTrace source configuration = 0 := by
  change currentJointShellResidualSection source configuration = 0 ↔ _
  exact
    (residualTransport_fixed_iff_zero_residual
      (currentJointShellResidualKeep source)
      (currentJointShellResidualKeep_active source)
      (currentJointShellResidualSection source configuration)).symm.trans
    (residualTransport_fixed_iff_zero_trace
      (currentJointShellResidualKeep source)
      (currentJointShellResidualKeep_active source)
      (currentJointShellResidualSection source configuration))

/-- Combining Layer 0/1 with the existing zero-fiber classification: the
forced trace vanishes exactly when all nine named strong equations hold. -/
theorem currentJointShellResidualTrace_zero_iff_strongEquation
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    currentJointShellResidualTrace source configuration = 0 ↔
      CurrentStrongJointShellEquation source configuration :=
  (currentJointShellZeroFiber_iff_trace_zero source configuration).symm.trans
    (currentJointShellZeroFiber_iff_strongEquation source configuration)

/-- Negative regression/no-third-sink boundary: a configuration outside the
joint zero fiber has a nonzero forced trace. -/
theorem currentJointShellResidualTrace_ne_zero_of_not_zeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (notZeroFiber : ¬ CurrentJointShellZeroFiber source configuration) :
    currentJointShellResidualTrace source configuration ≠ 0 := by
  intro traceZero
  exact notZeroFiber
    ((currentJointShellZeroFiber_iff_trace_zero source configuration).mpr
      traceZero)

end

end SaturationMonoid.PhysicsCore.StageNineJointShellResidualTransportRoot
