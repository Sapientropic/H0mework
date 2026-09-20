import H0mework.Physics.SynchronizedJoint.CoframeContactLocalActualLift
import H0mework.Physics.JointVariation.LiveElectricGlobalDevelopmentOperator

/-!
# Complete-joint synchronized Cartan--EC global operator

This module owns the generic source/current-only composition

```text
current
  -> temporal matter/scalar/adjoint write
  -> P286 algebraic and live-electric writes
  -> one synchronized Cartan--EC coframe/connection write at the canonical
     origin
  -> one global affine-coframe/affine-connection actual.
```

The constructor accepts only `(source,current)`.  It consumes no residual,
support coordinate, target jet, branch, zero-fiber witness, or free
coefficient.  Full-occurrence recentering and diagonal assembly remain
downstream producers; this module supplies their dependency-light canonical
origin action write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricCartanECSynchronizedGlobalOperator

open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicField
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-! ## Generic source/current-only joint tail -/

/-- The already generated post-MSA/post-P286-live current.  It is the exact
input of the synchronized joint gravity tail, not a second world. -/
def completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current source current

/-- The complete-joint pre-Cartan current preserves the supplied primitive
coframe as a whole field.  This is the dependency-light seam needed by later
full-occurrence assembly; it is not a pointwise supplied identification. -/
@[simp] theorem completeJointLiveElectricCartanECSynchronizedPreCartanCurrent_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
      source current).coframe = current.coframe := by
  rw [completeJointLiveElectricCartanECSynchronizedPreCartanCurrent,
    completeJointLiveElectricGlobalP286Current]
  change
    (diracDualFormNativeP286CanonicalGeneratedActual source
      (completeJointGlobalTemporalCurrent source current)).coframe = _
  rw [diracDualFormNativeP286CanonicalGeneratedActual_coframe,
    completeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe]

/-- One source/current-only global write with a synchronized Cartan--EC tail.
The canonical origin is internal to the fixed spacetime carrier. -/
def
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
    source
    (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
      source current)
    0

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
      source current).gaugeConnection =
      (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
        source current).gaugeConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
      source current).gaugeAuxiliary =
      (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
        source current).gaugeAuxiliary :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
      source current).scalar =
      (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
        source current).scalar :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
      source current).matter =
      (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
        source current).matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
      source current).conjugateMatter =
      (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
        source current).conjugateMatter :=
  rfl

/-- The coframe written by the global operator is the one explicit smooth
affine field generated by the synchronized action leg. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_coframe_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    ContDiff ℝ ∞
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
        source current).coframe := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contDiff
      source
      (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
        source current)
      0

/-- The same one global actual satisfies computed-`II+` simplicity at every
spacetime point. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
        source current) := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_simplicity
      source
      (completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
        source current)
      0

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
