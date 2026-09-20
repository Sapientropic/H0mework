import H0mework.Physics.IdentityHessian.CartanECNormalJointLocalActualLift
import H0mework.Physics.MatterCurrent.FullSynchronizedCompleteP286CauchyPath

/-!
# Whole-slice contact update from the repaired gravity action

KIN-14 closes one identity contact after a source/action-generated coframe
Hessian write, a live Cartan restart, and the EC-normal curvature write.  This
module applies that same constructor independently at every spatial contact
of one Cauchy current and assembles the generated contact values into a new
instantaneous current.

The public constructors consume only `(source, current)`.  In particular,
they do not accept a residual, response, target curvature, stationary
configuration, branch, gluing witness, or cohomology class.  For an
identity-coframe current the generated local actual at every spatial contact
has the repaired simplicity and auxiliary equations, the complete coframe
Euler equation, and the Cartan torsion--spin equation on that same contact.

This is a whole-slice family of actual local germs and a source-generated
Cauchy update.  It is not yet a single holonomically glued spacetime field,
a positive-time state-dependent integral curve, a global action-domain
receipt, or a whole-pointwise stationary family.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalJointLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineTopologicalLorentzThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

/-! ## Source/current-only local family and current write -/

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Repaired-root KIN-14 actual generated at one selected spatial contact. -/
def sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift
    source
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source current space)

/-- Canonical time-zero restriction of the generated local actual. -/
def sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineCauchyState :=
  canonicalCauchyRestriction 0
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
      source current space)

/-- Assemble every generated contact value into one instantaneous current.
The scalar velocity is read from the same local actual, rather than copied
from the input current. -/
def sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineCauchyState where
  coframe := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).coframe 0
  gravityConnection := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).gravityConnection 0
  gravityAuxiliary := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).gravitySimplicityMultiplier 0
  gaugeConnection := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).gaugeConnection 0
  gaugeAuxiliary := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).gaugeAuxiliary 0
  scalar := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).scalar 0
  scalarVelocity := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).scalarVelocity 0
  matter := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).matter 0
  conjugateMatter := fun space =>
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).conjugateMatter 0

/-- Every field of the assembled current is read from the generated local
actual at that same spatial contact.  This is the faithful diagonal assembly
seam; it does not assert compatibility between distinct local germs. -/
theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    let output :=
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
        source current
    let final :=
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space
    output.coframe space = final.coframe 0 /\
      output.gravityConnection space = final.gravityConnection 0 /\
      output.gravityAuxiliary space = final.gravityAuxiliary 0 /\
      output.gravitySimplicityMultiplier space =
        final.gravitySimplicityMultiplier 0 /\
      output.gaugeConnection space = final.gaugeConnection 0 /\
      output.gaugeAuxiliary space = final.gaugeAuxiliary 0 /\
      output.scalar space = final.scalar 0 /\
      output.scalarVelocity space =
        fieldDirectionalDerivative final.scalar 0
          canonicalLorentzianTimeDirection /\
      output.matter space = final.matter 0 /\
      output.conjugateMatter space = final.conjugateMatter 0 := by
  simp only [
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent,
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice,
    canonicalCauchyRestriction, canonicalCauchySlicePoint_zero_zero]
  simp

/-! ## Primitive fidelity and generated second jet -/

@[simp] theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_coframe_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
      source current space).coframe 0 = current.coframe space := by
  unfold
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
  rw [
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift_coframe]
  unfold sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  rw [identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin]
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      source current).coframe space = current.coframe space := by
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice
      source current space).coframe 0 = current.coframe space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
      source current space).coframe (canonicalCauchySlicePoint 0 0) =
        current.coframe space
  rw [canonicalCauchySlicePoint_zero_zero]
  exact
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_coframe_origin
      source current space

/-- The local actual retains all five non-gravity primitive fields from the
same source/action local base.  This is exact field provenance, not an old
equation receipt. -/
theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    let final :=
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space
    let base := sourceActionGeneratedJointLocalActualLift source current space
    final.gaugeConnection = base.gaugeConnection /\
      final.gaugeAuxiliary = base.gaugeAuxiliary /\
      final.scalar = base.scalar /\
      final.matter = base.matter /\
      final.conjugateMatter = base.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every contact carries the literal Hessian generated from its live
repaired-action load. -/
theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_coframeSecondJet
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    let base :=
      sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source current space
    coframeOriginSecondFrechetJet
        (fun point =>
          (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
            source current space).coframe point - base.coframe point) =
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        source base).1 := by
  exact
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift_coframe_secondJet
      source
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source current space)

/-! ## Same-contact repaired-root closure -/

theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space) :=
  sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift_simplicity
    source
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source current space)

theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space) :=
  sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift_auxiliaryEquation
    source
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source current space)

theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_fullCoframeEuler_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (coframeOne : current.coframe space = 1) :
    diracDualFormNativeCoframeEulerCovector source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
            source current space) 0) = 0 := by
  apply
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift_fullCoframeEuler_zero
  change current.coframe space = 1
  exact coframeOne

/-- The complete covector equation yields the twelve spatial-column and four
temporal-column Cauchy rows on the same generated actual.  These are readouts
of the full Euler equation, not additional independent constraints. -/
theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_cauchyRows_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (coframeOne : current.coframe space = 1) :
    let euler :=
      diracDualFormNativeCoframeEulerCovector source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
            source current space) 0)
    identityECSpatialCoframeCoordinatesOfCovector euler = 0 /\
      identityECConstraintCoordinatesOfCovector euler = 0 := by
  have eulerZero :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_fullCoframeEuler_zero
      source current space coframeOne
  rw [eulerZero]
  exact ⟨rfl, rfl⟩

theorem
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_torsionSpin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (coframeOne : current.coframe space = 1) :
    let final :=
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (final.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt final.coframe 0)
              (final.gravityConnection 0))) =
        formNativePhysicalSpinCurrentThreeForm source 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus final) 0) := by
  apply
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift_torsionSpin_zero
  change Matrix.det (current.coframe space) ≠ 0
  rw [coframeOne]
  norm_num

/-! ## Fixed exact-lineage whole-slice checkpoint -/

def positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent :
    StageNineCauchyState :=
  sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentFullSynchronizedCauchyState

private theorem
    positiveP506MatterCurrentFullSynchronizedCauchyState_coframe_one
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentFullSynchronizedCauchyState.coframe space = 1 := by
  change
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
        (canonicalCauchySlicePoint 0 space) = 1
  exact
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
      (canonicalCauchySlicePoint 0 space)

theorem
    positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_coframe_one
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.coframe
        space = 1 := by
  unfold positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
  rw [
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_coframe]
  exact positiveP506MatterCurrentFullSynchronizedCauchyState_coframe_one space

/-- Fixed no-premise checkpoint.  H1 is deliberately absent: it remains the
automatic readout of the already generated occurrence ring and is neither a
premise nor a field of this physical producer. -/
theorem
    positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceContactUpdate_realizes :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference /\
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 /\
      (forall space : StageNineSpatialPoint,
        let final :=
          sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentFullSynchronizedCauchyState space
        FormNativeGravitySimplicityEquation final /\
          FormNativeGravityAuxiliaryEquation final /\
          diracDualFormNativeCoframeEulerCovector
              positiveSmoothUnifiedSource 0
              (toContinuumPointField final 0) = 0 /\
          internalBivectorDualThreeForm
              (torsionCoframeWedgeThreeForm
                (final.coframe 0)
                (pointwiseCartanTorsion
                  (holonomicCoframeFirstJetAt final.coframe 0)
                  (final.gravityConnection 0))) =
            formNativePhysicalSpinCurrentThreeForm
              positiveSmoothUnifiedSource 0 0
              (toContinuumPointField
                (restrictHolonomicConfigurationToIIPlus final) 0)) /\
      (forall space : StageNineSpatialPoint,
        let output :=
          positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
        let final :=
          sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentFullSynchronizedCauchyState space
        output.coframe space = final.coframe 0 /\
          output.gravityConnection space = final.gravityConnection 0 /\
          output.gravityAuxiliary space = final.gravityAuxiliary 0 /\
          output.gravitySimplicityMultiplier space =
            final.gravitySimplicityMultiplier 0 /\
          output.gaugeConnection space = final.gaugeConnection 0 /\
          output.gaugeAuxiliary space = final.gaugeAuxiliary 0 /\
          output.scalar space = final.scalar 0 /\
          output.scalarVelocity space =
            fieldDirectionalDerivative final.scalar 0
              canonicalLorentzianTimeDirection /\
          output.matter space = final.matter 0 /\
          output.conjugateMatter space = final.conjugateMatter 0) := by
  refine
    ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      positiveSmoothUnifiedSource_generates_endpoint_eleven, ?_, ?_⟩
  · intro space
    have coframeOne :=
      positiveP506MatterCurrentFullSynchronizedCauchyState_coframe_one space
    exact
      ⟨sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_simplicity
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState space,
        sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_auxiliaryEquation
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState space,
        sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_fullCoframeEuler_zero
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState space coframeOne,
        sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_torsionSpin_zero
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState space coframeOne⟩
  · intro space
    exact
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
