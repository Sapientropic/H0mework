import H0mework.Physics.ConstitutiveAction.ResponseOperator
import H0mework.Physics.DualVariation.RepairedMatterResponseOperator

/-!
# Repaired-root constitutive joint action operator

This module upgrades the existing constitutive response path without reading
its downstream residual:

```text
source + current
  -> repaired primal/adjoint action write
  -> source/current-owned constitutive auxiliary
  -> repaired-root Einstein--Cartan recomputation
  -> one common holonomic actual.
```

The order is chosen so the repaired matter response is generated from the
smooth supplied current.  The constitutive write does not change any field
used by either matter action law, and its auxiliary is still computed from
the same current coframe and gauge curvature.  No residual coordinate,
support, sign, branch, target derivative, or zero-fiber witness is accepted.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- First solve both repaired-root matter evolution laws on the supplied
current. -/
def diracDualFormNativeRepairedMatterWrittenCurrent
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualRepairedMatterJointResponseActual current

@[simp] theorem diracDualFormNativeRepairedMatterWrittenCurrent_coframe
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedMatterWrittenCurrent current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedMatterWrittenCurrent_gravityConnection
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedMatterWrittenCurrent current
      ).gravityConnection =
      current.gravityConnection :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedMatterWrittenCurrent_gaugeConnection
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedMatterWrittenCurrent current).gaugeConnection =
      current.gaugeConnection :=
  rfl

@[simp] theorem diracDualFormNativeRepairedMatterWrittenCurrent_scalar
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedMatterWrittenCurrent current).scalar =
      current.scalar :=
  rfl

/-- Install the same action-owned constitutive auxiliary after the repaired
matter write.  Its input coframe and gauge curvature are unchanged. -/
def diracDualFormNativeRepairedConstitutiveWrittenCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeRepairedMatterWrittenCurrent current with
    gaugeAuxiliary :=
      diracDualFormNativeConstitutiveAuxiliaryField source current }

@[simp] theorem diracDualFormNativeRepairedConstitutiveWrittenCurrent_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current
      ).coframe = current.coframe :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_gravityConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current
      ).gravityConnection = current.gravityConnection :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current
      ).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem diracDualFormNativeRepairedConstitutiveWrittenCurrent_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current
      ).scalar = current.scalar :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current
      ).conjugateMatter =
      (diracDualFormNativeRepairedMatterWrittenCurrent current
        ).conjugateMatter :=
  rfl

/-- One branch-free repaired constitutive/Einstein--Cartan response. -/
def diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source
    (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current)

theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source current) :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity _ _

theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source current) :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
    _ _

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).gaugeConnection =
      current.gaugeConnection :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField source current :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).scalar =
      current.scalar :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).matter =
      (diracDualFormNativeRepairedMatterWrittenCurrent current).matter :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).conjugateMatter =
      (diracDualFormNativeRepairedMatterWrittenCurrent current
        ).conjugateMatter :=
  rfl

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityConnection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).gravityConnection 0 =
      current.gravityConnection 0 := by
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero]
  rfl

theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_primalActionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source current)
      0
      (holonomicMatterCovariantDerivative
        (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
          source current)
        0 canonicalLorentzianTimeDirection) := by
  have law :=
    actionGeneratedDiracDualRepairedMatterJointResponseActual_primalActionLaw
      current smooth noncharacteristic
  change
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (diracDualFormNativeRepairedMatterWrittenCurrent current)
      0
      (holonomicMatterCovariantDerivative
        (diracDualFormNativeRepairedMatterWrittenCurrent current)
        0 canonicalLorentzianTimeDirection) at law
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at law ⊢
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector at law ⊢
  have derivativeEq :
      ∀ direction,
        holonomicMatterCovariantDerivative
            (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
              source current)
            0 direction =
          holonomicMatterCovariantDerivative
            (diracDualFormNativeRepairedMatterWrittenCurrent current)
            0 direction := by
    intro direction
    unfold holonomicMatterCovariantDerivative
    rw [
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_matter,
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityConnection_zero,
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection,
      diracDualFormNativeRepairedMatterWrittenCurrent_gravityConnection,
      diracDualFormNativeRepairedMatterWrittenCurrent_gaugeConnection]
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_matter]
  simp_rw [derivativeEq]
  simpa only [
    diracDualFormNativeRepairedMatterWrittenCurrent_coframe,
    diracDualFormNativeRepairedMatterWrittenCurrent_scalar] using law

theorem
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_liveAdjointActionLaw_of_matterLaw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (law :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
        (diracDualFormNativeRepairedMatterWrittenCurrent current)
        0
        (holonomicConjugateMatterDerivativeDual
          (diracDualFormNativeRepairedMatterWrittenCurrent current)
          0 canonicalLorentzianTimeDirection)) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current)
      0
      (holonomicConjugateMatterDerivativeDual
        (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current)
        0 canonicalLorentzianTimeDirection) := by
  unfold HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw at law ⊢
  have conjugateDerivativeEq :
      ∀ direction,
        holonomicConjugateMatterDerivativeDual
            (diracDualFormNativeRepairedConstitutiveWrittenCurrent
              source current)
            0 direction =
          holonomicConjugateMatterDerivativeDual
            (diracDualFormNativeRepairedMatterWrittenCurrent current)
            0 direction := by
    intro direction
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_conjugateMatter]
  have algebraicEq :
      holonomicDiracDualLiveCoframeMatterAlgebraicOperator
          (diracDualFormNativeRepairedConstitutiveWrittenCurrent
            source current)
          0 =
        holonomicDiracDualLiveCoframeMatterAlgebraicOperator
          (diracDualFormNativeRepairedMatterWrittenCurrent current)
          0 := by
    unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
      holonomicIdentityCoframeMatterConnectionOperator
    rw [
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_coframe,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_gravityConnection,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_gaugeConnection,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_scalar,
      diracDualFormNativeRepairedMatterWrittenCurrent_coframe,
      diracDualFormNativeRepairedMatterWrittenCurrent_gravityConnection,
      diracDualFormNativeRepairedMatterWrittenCurrent_gaugeConnection,
      diracDualFormNativeRepairedMatterWrittenCurrent_scalar]
  simpa only [
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual,
    holonomicDiracDualLiveCoframeAlgebraicDual,
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates,
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates,
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates,
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates,
    holonomicLiveCoframeAffineGerm,
    holonomicConjugateMatterCoordinates,
    toContinuumPointField,
    generatedVolumeDensity,
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_coframe,
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_conjugateMatter,
    diracDualFormNativeRepairedMatterWrittenCurrent_coframe,
    conjugateDerivativeEq,
    algebraicEq] using law

theorem
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_liveAdjointActionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current)
      0
      (holonomicConjugateMatterDerivativeDual
        (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current)
        0 canonicalLorentzianTimeDirection) := by
  apply
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_liveAdjointActionLaw_of_matterLaw
  change
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (actionGeneratedDiracDualRepairedMatterJointResponseActual current)
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualRepairedMatterJointResponseActual current)
        0 canonicalLorentzianTimeDirection)
  exact
    actionGeneratedDiracDualRepairedMatterJointResponseActual_liveAdjointActionLaw
      current smooth nondegenerate noncharacteristic

theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_liveAdjointActionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source current)
      0
      (holonomicConjugateMatterDerivativeDual
        (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
          source current)
        0 canonicalLorentzianTimeDirection) := by
  have law :=
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_liveAdjointActionLaw
      source current smooth nondegenerate noncharacteristic
  unfold HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw at law ⊢
  have conjugateDerivativeEq :
      ∀ direction,
        holonomicConjugateMatterDerivativeDual
            (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
              source current)
            0 direction =
          holonomicConjugateMatterDerivativeDual
            (diracDualFormNativeRepairedConstitutiveWrittenCurrent
              source current)
            0 direction := by
    intro direction
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_conjugateMatter]
  have algebraicEq :
      holonomicDiracDualLiveCoframeMatterAlgebraicOperator
          (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
            source current)
          0 =
        holonomicDiracDualLiveCoframeMatterAlgebraicOperator
          (diracDualFormNativeRepairedConstitutiveWrittenCurrent source current)
          0 := by
    unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
      holonomicIdentityCoframeMatterConnectionOperator
    rw [
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe,
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityConnection_zero,
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection,
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_coframe,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_gravityConnection,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_gaugeConnection,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_scalar]
  simpa only [
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual,
    holonomicDiracDualLiveCoframeAlgebraicDual,
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates,
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates,
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates,
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates,
    holonomicLiveCoframeAffineGerm,
    holonomicConjugateMatterCoordinates,
    toContinuumPointField,
    generatedVolumeDensity,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_coframe,
    diracDualFormNativeRepairedConstitutiveWrittenCurrent_conjugateMatter,
    conjugateDerivativeEq,
    algebraicEq] using law

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
