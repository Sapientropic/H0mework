import H0mework.Physics.GravitySource.SpinOrbitCarrier
import H0mework.Physics.Admission.JointShellResidualCarrier

/-!
# S9-C3g7a: unique curvature obligation induced by residual transport

C3g6b closes the residual-level transport equations on the minimal
Spin-stable responsibility carrier.  This module asks what an actual
holonomic configuration must generate if it preserves the positive source's
coframe and simplicity mouth while realizing that transported residual.

No curvature is accepted from the source and no configuration is claimed to
exist here.  Instead, the already generated constitutive value and the actual
transported residual uniquely determine a required curvature:

`F_required = J(II+(e_source)) + K r`.

The source sigma is the only scalar in this expression.  The root split proves
that the old source curvature is `F_required + trace`, hence the nonzero forced
trace proves that the old mouth cannot masquerade as its own successor.

Finally, under a fixed-coframe and simplicity-mouth hypothesis, the actual
gravity-auxiliary projection of the current joint residual equals `K r` iff
the primitive Lorentz connection generates exactly `F_required`.  This is a
typed uniqueness/readout checkpoint, not yet the Layer-3 producer: the next
module must construct a primitive connection field whose genuine
`dω + ω∧ω` curvature has this value.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthTransportCurvature

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineHolonomicField
open StageNineGravityAuxiliaryVariation
open StageNineJointShellResidualCarrier
open StageNinePositiveSourceGravityMouthObstruction
open StageNinePositiveSourceGravityMouthSpinOrbitCarrier

noncomputable section

set_option autoImplicit false

/-- Current constitutive curvature at the fixed positive-source coframe
mouth. -/
def positiveSourceGravityMouthConstitutiveCurvature : PhysicalBivector :=
  gravityInternalDualEquiv
    (physicalIIPlusBivector
      (positiveSmoothUnifiedSource.legacy.coframeAt 0))

/-- Ambient readout of `K r` from the already transported carried residual. -/
def positiveSourceGravityMouthTransportedResidual : PhysicalBivector :=
  carriedPositiveSourceGravityMouthSpinOrbitObstruction |> fun residual =>
    (positiveSourceGravityMouthSpinOrbitResponsibilityKeep residual).1

theorem positiveSourceGravityMouthTransportedResidual_eq_scalarKeep :
    positiveSourceGravityMouthTransportedResidual =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        positiveSourceGravityMouthObstruction := by
  rfl

/-- The unique curvature value compatible with the same constitutive mouth
and the first residual step.  This is a derived obligation, not a source
field. -/
def positiveSourceGravityMouthRequiredCurvature : PhysicalBivector :=
  positiveSourceGravityMouthConstitutiveCurvature +
    positiveSourceGravityMouthTransportedResidual

/-- Pure uniqueness: a candidate curvature has transported residual exactly
when it is the derived required curvature. -/
theorem candidateCurvature_residual_eq_transported_iff
    (candidateCurvature : PhysicalBivector) :
    candidateCurvature - positiveSourceGravityMouthConstitutiveCurvature =
        positiveSourceGravityMouthTransportedResidual ↔
      candidateCurvature = positiveSourceGravityMouthRequiredCurvature := by
  constructor
  · intro residualEquality
    rw [positiveSourceGravityMouthRequiredCurvature, ← residualEquality]
    abel
  · intro curvatureEquality
    rw [curvatureEquality, positiveSourceGravityMouthRequiredCurvature]
    abel

theorem positiveSourceGravityMouthObstruction_eq_source_sub_constitutive :
    positiveSourceGravityMouthObstruction =
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin -
        positiveSourceGravityMouthConstitutiveCurvature :=
  rfl

/-- The framework split becomes an exact curvature balance: the forced trace
is precisely the responsibility separating the old source curvature from the
required successor curvature. -/
theorem positiveSourceGravityMouthSourceCurvature_eq_required_add_trace :
    positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin =
      positiveSourceGravityMouthRequiredCurvature +
        (linearResidualTrace
          positiveSourceGravityMouthSpinOrbitResponsibilityKeep
          carriedPositiveSourceGravityMouthSpinOrbitObstruction).1 := by
  have split := congrArg Subtype.val
    carriedPositiveSourceGravityMouthSpinOrbitObstruction_split
  change
    positiveSourceGravityMouthObstruction =
        positiveSourceGravityMouthTransportedResidual +
          (linearResidualTrace
            positiveSourceGravityMouthSpinOrbitResponsibilityKeep
            carriedPositiveSourceGravityMouthSpinOrbitObstruction).1 at split
  rw [positiveSourceGravityMouthObstruction_eq_source_sub_constitutive] at split
  rw [positiveSourceGravityMouthRequiredCurvature]
  have restored := (sub_eq_iff_eq_add).mp split
  simpa [add_assoc, add_comm, add_left_comm] using restored

/-- Negative regression: the nonzero trace forbids identifying the required
successor curvature with the old source curvature. -/
theorem positiveSourceGravityMouthRequiredCurvature_ne_sourceCurvature :
    positiveSourceGravityMouthRequiredCurvature ≠
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin := by
  intro requiredIsOld
  have sourceSplit :=
    positiveSourceGravityMouthSourceCurvature_eq_required_add_trace
  rw [← requiredIsOld] at sourceSplit
  have traceValueZero :
      (linearResidualTrace
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        carriedPositiveSourceGravityMouthSpinOrbitObstruction).1 = 0 := by
    have cancelled := congrArg
      (fun curvature : PhysicalBivector =>
        curvature - positiveSourceGravityMouthRequiredCurvature)
      sourceSplit
    simpa using cancelled.symm
  apply carriedPositiveSourceGravityMouthSpinOrbitObstruction_trace_ne_zero
  apply Subtype.ext
  exact traceValueZero

/-- Equivalent residual-form regression: the unchanged old mouth has residual
`r`, not the transported residual `K r`. -/
theorem positiveSourceGravityMouthSourceResidual_ne_transported :
    positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin -
        positiveSourceGravityMouthConstitutiveCurvature ≠
      positiveSourceGravityMouthTransportedResidual := by
  intro oldResidualTransported
  have oldCurvatureRequired :=
    (candidateCurvature_residual_eq_transported_iff
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin).mp
      oldResidualTransported
  exact positiveSourceGravityMouthRequiredCurvature_ne_sourceCurvature
    oldCurvatureRequired.symm

/-- Actual gravity-mouth residual read from primitive coframe and generated
holonomic curvature. -/
def stageNineGravityMouthResidualAt
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : PhysicalBivector :=
  holonomicGravityCurvature configuration point -
    gravityInternalDualEquiv
      (physicalIIPlusBivector (configuration.coframe point))

/-- Fixed coframe jurisdiction for this first connection-lift step. -/
def PreservesPositiveSourceCoframeAtOrigin
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  configuration.coframe 0 =
    positiveSmoothUnifiedSource.legacy.coframeAt 0

/-- Under the fixed source coframe, realizing `K r` is equivalent to
generating the unique required curvature. -/
theorem stageNineGravityMouthResidualAt_eq_transported_iff
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe : PreservesPositiveSourceCoframeAtOrigin configuration) :
    stageNineGravityMouthResidualAt configuration 0 =
        positiveSourceGravityMouthTransportedResidual ↔
      holonomicGravityCurvature configuration 0 =
        positiveSourceGravityMouthRequiredCurvature := by
  unfold PreservesPositiveSourceCoframeAtOrigin at preservesCoframe
  unfold stageNineGravityMouthResidualAt
  rw [preservesCoframe]
  exact candidateCurvature_residual_eq_transported_iff
    (holonomicGravityCurvature configuration 0)

/-- On the simplicity mouth, the gravity-auxiliary coordinate of the actual
joint residual is exactly the gravity-mouth residual above. -/
theorem currentGravityAuxiliaryProjection_eq_gravityMouthResidual
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (simplicityMouth : configuration.gravityAuxiliary point =
      physicalIIPlusBivector (configuration.coframe point)) :
    (currentPointwiseAlgebraicResidual source configuration point).gravityAuxiliary =
      stageNineGravityMouthResidualAt configuration point := by
  simp [currentPointwiseAlgebraicResidual,
    holonomicGravityAuxiliaryEquationResidual,
    gravityAuxiliaryEquationResidual, toContinuumPointField,
    stageNineGravityMouthResidualAt, simplicityMouth]

/-- Final typed obligation for the next producer: under coframe preservation
and actual simplicity, the joint projection transports iff the primitive
connection generates the required curvature. -/
theorem currentGravityAuxiliaryProjection_eq_transported_iff
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe : PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          configuration 0).gravityAuxiliary =
        positiveSourceGravityMouthTransportedResidual ↔
      holonomicGravityCurvature configuration 0 =
        positiveSourceGravityMouthRequiredCurvature := by
  rw [currentGravityAuxiliaryProjection_eq_gravityMouthResidual
    positiveSmoothUnifiedSource configuration 0 simplicityMouth]
  exact stageNineGravityMouthResidualAt_eq_transported_iff
    configuration preservesCoframe

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthTransportCurvature
