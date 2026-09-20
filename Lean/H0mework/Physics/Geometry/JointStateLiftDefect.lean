import H0mework.Physics.GravitySource.JointResidualDelta
import H0mework.Physics.Admission.JointShellResidualTransportRoot

/-!
# S9-C3h6a: typed Stage-9 joint state-lift defect

The framework starts from the residual transport law

`r' = K r`, `r = K r + (I-K)r`, `trace = (I-K)r`.

A configuration map is therefore a residual-transport lift only when its
*actual* residual readout makes the square commute:

`R (U x) = K (R x)`.

This module records the obstruction to that square as

`D_U(x) = R(Ux) - K(Rx) = (R(Ux)-R(x)) + trace(x)`.

Consequently `D_U(x)=0` exactly when the actual configuration displacement is
the negative forced trace.  No zero-fiber witness, target state, source slot,
repair field, or transport certificate is stored in the definition.

The existing normalized-affine connection installer is then classified by
this obstruction.  Its four connection-invariant coordinates retain their
entire forced-trace responsibility in `D_U`; the remaining five coordinates
contain the actual action-induced response plus that trace.  This rejects or
localizes a candidate state lift.  It does not turn zero residuals into
producer premises and does not yet derive a repair carrier.
-/

namespace SaturationMonoid.PhysicsCore.StageNineJointStateLiftDefect

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNinePositiveSourceGravityMouthJointResidualDelta

noncomputable section

set_option autoImplicit false

abbrev AuditSmoothUnifiedSource :=
  StageNineJointShellResidualCarrier.CurrentSmoothUnifiedSource

/-- A genuine state update acts on the existing holonomic configuration
carrier.  This type contains neither a residual nor a proof. -/
abbrev CurrentJointShellStateUpdate :=
  StageNineHolonomicConfiguration → StageNineHolonomicConfiguration

/-- Actual residual displacement caused by a state update. -/
def currentJointShellActualResidualDelta
    (source : AuditSmoothUnifiedSource)
    (update : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellResidualSection :=
  currentJointShellResidualSection source (update configuration) -
    currentJointShellResidualSection source configuration

/-- Obstruction to lifting the source-generated residual keep to an actual
configuration update. -/
def currentJointShellStateLiftDefect
    (source : AuditSmoothUnifiedSource)
    (update : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellResidualSection :=
  currentJointShellResidualSection source (update configuration) -
    currentJointShellResidualKeep source
      (currentJointShellResidualSection source configuration)

/-- The commuting-square statement itself.  This is a proposition read from
an actual update, not a certificate field accepted by a producer. -/
def CurrentJointShellResidualTransportLiftAt
    (source : AuditSmoothUnifiedSource)
    (update : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  currentJointShellResidualSection source (update configuration) =
    currentJointShellResidualKeep source
      (currentJointShellResidualSection source configuration)

/-- The physical commuting square is exactly a lift of the domain-native
full-joint residual process.  This keeps the responsibilities separate:
`currentJointShellResidualEffectiveProcess` produces `r ↦ K r`, while the
physical update must realize that already-forced successor under `R`. -/
theorem currentJointShellResidualTransportLiftAt_iff_liftsEffectiveProcess
    (source : AuditSmoothUnifiedSource)
    (update : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellResidualTransportLiftAt source update configuration ↔
      currentJointShellResidualSection source (update configuration) =
        (currentJointShellResidualEffectiveProcess source).update
          (currentJointShellResidualSection source configuration) := by
  rfl

/-- Exact state-level form of the first formula:
`D_U = actualDelta + (I-K)R`. -/
theorem currentJointShellStateLiftDefect_eq_actualDelta_add_trace
    (source : AuditSmoothUnifiedSource)
    (update : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration) :
    currentJointShellStateLiftDefect source update configuration =
      currentJointShellActualResidualDelta source update configuration +
        currentJointShellResidualTrace source configuration := by
  unfold currentJointShellStateLiftDefect currentJointShellActualResidualDelta
  rw [currentJointShellResidualTrace_eq_id_sub_keep]
  abel

/-- Vanishing lift defect is definitionally equivalent to the genuine
configuration/residual commuting square. -/
theorem currentJointShellStateLiftDefect_eq_zero_iff_transportLift
    (source : AuditSmoothUnifiedSource)
    (update : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration) :
    currentJointShellStateLiftDefect source update configuration = 0 ↔
      CurrentJointShellResidualTransportLiftAt source update configuration := by
  unfold currentJointShellStateLiftDefect
    CurrentJointShellResidualTransportLiftAt
  exact sub_eq_zero

/-- Equivalent displacement hard gate: an actual state update transports the
residual exactly when its residual displacement realizes the negative forced
trace. -/
theorem currentJointShellStateLiftDefect_eq_zero_iff_delta_eq_neg_trace
    (source : AuditSmoothUnifiedSource)
    (update : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration) :
    currentJointShellStateLiftDefect source update configuration = 0 ↔
      currentJointShellActualResidualDelta source update configuration =
        -currentJointShellResidualTrace source configuration := by
  rw [currentJointShellStateLiftDefect_eq_actualDelta_add_trace]
  exact add_eq_zero_iff_eq_neg

/-! ## Classification of the existing connection-only candidate -/

/-- The existing normalized-affine connection installer, now explicitly
viewed only as one candidate state update. -/
def normalizedAffineConnectionOnlyStateUpdate : CurrentJointShellStateUpdate :=
  installedConfiguration

abbrev normalizedAffineConnectionOnlyJointStateLiftDefect
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellResidualSection :=
  currentJointShellStateLiftDefect source
    normalizedAffineConnectionOnlyStateUpdate configuration

/-- The manually exposed nine coordinates are exactly the additive
displacement of the actual residual readout. -/
theorem installedJointResidualDelta_eq_actual_sub
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    installedJointResidualDelta source configuration point =
      currentPointwiseJointShellResidual source
          (installedConfiguration configuration) point -
        currentPointwiseJointShellResidual source configuration point := by
  apply CurrentPointwiseJointShellResidualCarrier.ext
  · apply CurrentPointwiseAlgebraicResidualCarrier.ext <;> rfl
  · apply CurrentPointwiseEulerLagrangeResidualCarrier.ext <;> rfl

/-- Pointwise defect equals the actual typed residual delta plus the forced
trace. -/
theorem normalizedAffineConnectionOnlyJointStateLiftDefect_eq_delta_add_trace
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
        point =
      installedJointResidualDelta source configuration point +
        currentJointShellResidualTrace source configuration point := by
  have split := congrFun
    (currentJointShellStateLiftDefect_eq_actualDelta_add_trace source
      normalizedAffineConnectionOnlyStateUpdate configuration) point
  change
    normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
        point =
      (currentPointwiseJointShellResidual source
          (installedConfiguration configuration) point -
        currentPointwiseJointShellResidual source configuration point) +
          currentJointShellResidualTrace source configuration point at split
  rw [← installedJointResidualDelta_eq_actual_sub] at split
  exact split

/-- The five-coordinate support theorem is reinterpreted as a lift-defect
decomposition, not as a claim that the other four residuals must be supplied
as zero. -/
theorem normalizedAffineConnectionOnlyJointStateLiftDefect_eq_sensitiveDelta_add_trace
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
        point =
      embedInstalledSensitiveResidualDelta
          (installedSensitiveResidualDelta source configuration point) +
        currentJointShellResidualTrace source configuration point := by
  rw [normalizedAffineConnectionOnlyJointStateLiftDefect_eq_delta_add_trace,
    installedJointResidualDelta_eq_embed_sensitive]

/-- The connection-invariant gravity-simplicity coordinate leaves its whole
forced trace in the lift defect. -/
theorem normalizedAffineConnectionOnlyLiftDefect_gravitySimplicity_eq_trace
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
      point).algebraic.gravitySimplicity =
      (currentJointShellResidualTrace source configuration
        point).algebraic.gravitySimplicity := by
  rw [normalizedAffineConnectionOnlyJointStateLiftDefect_eq_delta_add_trace]
  change
    (installedJointResidualDelta source configuration
        point).algebraic.gravitySimplicity +
      (currentJointShellResidualTrace source configuration
        point).algebraic.gravitySimplicity = _
  rw [installed_gravitySimplicity_delta_zero]
  exact zero_add _

/-- The connection-invariant P286 auxiliary coordinate likewise retains its
full trace responsibility. -/
theorem normalizedAffineConnectionOnlyLiftDefect_p286GaugeAuxiliary_eq_trace
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
      point).algebraic.p286GaugeAuxiliary =
      (currentJointShellResidualTrace source configuration
        point).algebraic.p286GaugeAuxiliary := by
  rw [normalizedAffineConnectionOnlyJointStateLiftDefect_eq_delta_add_trace]
  change
    (installedJointResidualDelta source configuration
        point).algebraic.p286GaugeAuxiliary +
      (currentJointShellResidualTrace source configuration
        point).algebraic.p286GaugeAuxiliary = _
  rw [installed_p286GaugeAuxiliary_delta_zero]
  exact zero_add _

/-- The connection-invariant P286 connection EL coordinate retains its full
trace responsibility. -/
theorem normalizedAffineConnectionOnlyLiftDefect_p286GaugeConnection_eq_trace
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
      point).eulerLagrange.p286GaugeConnection =
      (currentJointShellResidualTrace source configuration
        point).eulerLagrange.p286GaugeConnection := by
  rw [normalizedAffineConnectionOnlyJointStateLiftDefect_eq_delta_add_trace]
  change
    (installedJointResidualDelta source configuration
        point).eulerLagrange.p286GaugeConnection +
      (currentJointShellResidualTrace source configuration
        point).eulerLagrange.p286GaugeConnection = _
  rw [installed_p286GaugeConnection_delta_zero]
  exact zero_add _

/-- The connection-invariant scalar EL coordinate retains its full forced
trace responsibility. -/
theorem normalizedAffineConnectionOnlyLiftDefect_scalar_eq_trace
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
      point).eulerLagrange.scalar =
      (currentJointShellResidualTrace source configuration
        point).eulerLagrange.scalar := by
  rw [normalizedAffineConnectionOnlyJointStateLiftDefect_eq_delta_add_trace]
  change
    (installedJointResidualDelta source configuration
        point).eulerLagrange.scalar +
      (currentJointShellResidualTrace source configuration
        point).eulerLagrange.scalar = _
  rw [installed_scalar_delta_zero]
  exact zero_add _

/-- Negative regression in the correct direction: any nonzero trace on an
invariant coordinate is a nonzero lift defect for this candidate update.
This rejects the candidate instead of demanding a zero residual premise. -/
theorem normalizedAffineConnectionOnlyJointStateLiftDefect_ne_zero_of_invariantTrace
    (source : AuditSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nonzeroTrace :
      (currentJointShellResidualTrace source configuration
          point).algebraic.gravitySimplicity ≠ 0 ∨
        (currentJointShellResidualTrace source configuration
          point).algebraic.p286GaugeAuxiliary ≠ 0 ∨
        (currentJointShellResidualTrace source configuration
          point).eulerLagrange.p286GaugeConnection ≠ 0 ∨
        (currentJointShellResidualTrace source configuration
          point).eulerLagrange.scalar ≠ 0) :
    normalizedAffineConnectionOnlyJointStateLiftDefect source configuration
        point ≠ 0 := by
  intro defectZero
  rcases nonzeroTrace with h | h | h | h
  · apply h
    rw [← normalizedAffineConnectionOnlyLiftDefect_gravitySimplicity_eq_trace]
    exact congrArg
      (fun residual : CurrentPointwiseJointShellResidualCarrier =>
        residual.algebraic.gravitySimplicity) defectZero
  · apply h
    rw [← normalizedAffineConnectionOnlyLiftDefect_p286GaugeAuxiliary_eq_trace]
    exact congrArg
      (fun residual : CurrentPointwiseJointShellResidualCarrier =>
        residual.algebraic.p286GaugeAuxiliary) defectZero
  · apply h
    rw [← normalizedAffineConnectionOnlyLiftDefect_p286GaugeConnection_eq_trace]
    exact congrArg
      (fun residual : CurrentPointwiseJointShellResidualCarrier =>
        residual.eulerLagrange.p286GaugeConnection) defectZero
  · apply h
    rw [← normalizedAffineConnectionOnlyLiftDefect_scalar_eq_trace]
    exact congrArg
      (fun residual : CurrentPointwiseJointShellResidualCarrier =>
        residual.eulerLagrange.scalar) defectZero

end

end SaturationMonoid.PhysicsCore.StageNineJointStateLiftDefect
