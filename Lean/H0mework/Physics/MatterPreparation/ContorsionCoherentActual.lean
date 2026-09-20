import H0mework.Physics.CurrentAction.LorentzCoherentDiagonalActualCore
import H0mework.Physics.MatterPreparation.ContorsionFreshResponseTangentSimplicity

/-!
# S9-C3h200r: one coherent whole-domain actual from the final Lorentz current

C3h200p generated the complete contact-local response from the corrected
final current, and C3h200q checked regenerated tangent simplicity on its
canonical local actual.  This module now feeds that same current and response
into the existing coherent-diagonal constructor:

```text
C3h200n final actual
→ its exact zero-slice current Ufinal
→ state-dependent complete V(Ufinal) at every contact
→ one whole-domain actual Acoh(Ufinal)
→ exact final-actual zero slice
→ genuine same-actual simplicity tangent at the common contact.
```

The constructor is source/action-first and branch-free.  It realizes all
nine primitive holonomic fields of the update on one spacetime carrier; the
derived Cauchy `scalarVelocity` remains outside primitive slice fidelity, as
in the generic coherent core.  This file does not infer Lorentz or P286 Gauss
from point-value fidelity: those constraints read spatial BF derivatives and
require their own same-actual regularity bridges.  It also does not claim a
flow or positive-time propagation.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCurrentCanonicalFullActionLorentzContactResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshResponseTangentSimplicity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzSameActualConstraints
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem
    preContorsionFullLorentzTriangularCurrent_responseUpdate_zero :
    currentCanonicalFullActionLorentzStateResponseUpdate
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0 =
      PreContorsionFullLorentzTriangularCurrent := by
  exact
    currentCanonicalFullActionLorentzStateResponseUpdate_zero_of_actionPrepared
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      preContorsionFullLorentzTriangularCurrent_actionPrepared

/-! ## Coherent final-current actual and its generated zero slice -/

/-- The one whole-domain primitive actual generated from the C3h200n final
current and its newly recomputed complete response. -/
def positiveP506MatterPreContorsionFullLorentzFreshCoherentActual :
    StageNineHolonomicConfiguration :=
  currentCanonicalFullActionLorentzCoherentDiagonalActual
    positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent

/-- Exact primitive zero-slice identity with the C3h200n final actual.  The
predicate deliberately lists only fields primitive in a holonomic actual;
it stores no equation or residual-zero receipt. -/
def PreContorsionFullLorentzFreshCoherentInitialSliceFidelity : Prop :=
  ∀ space,
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.coframe
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gravityConnection
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravityAuxiliary
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gravityAuxiliary
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravitySimplicityMultiplier
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gravitySimplicityMultiplier
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.scalar
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.scalar
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.matter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.matter
        (canonicalCauchySlicePoint 0 space) ∧
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space)

/-- The generic coherent constructor realizes the complete nine-field
primitive update generated from `Ufinal` at every time/contact pair. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_primitiveSliceFidelity :
    PrimitiveSliceFidelity
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent := by
  exact coherentDiagonalActual_primitiveSliceFidelity
    positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent

/-- Because `Ufinal` is action-prepared, the coherent actual starts from the
actual C3h200n zero slice, not from a projected or stale carrier. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_initialSliceFidelity :
    PreContorsionFullLorentzFreshCoherentInitialSliceFidelity := by
  intro space
  have slice :=
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_primitiveSliceFidelity
      0 space
  rw [preContorsionFullLorentzTriangularCurrent_responseUpdate_zero] at slice
  simpa only [PreContorsionFullLorentzTriangularCurrent,
    canonicalCauchyRestriction] using slice

/-- The action-generated triangular connection remains present on the
coherent actual's common origin.  Whole-domain diagonalization therefore did
not erase the final-current epoch. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_gravityConnection_origin :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravityConnection
        0 =
      lorentzSkewConnectionOfBivectorOneForm
        preContorsionFullLorentzConnectionCorrection := by
  have fidelity :=
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_initialSliceFidelity
      0
  rw [canonicalCauchySlicePoint_zero_zero] at fidelity
  exact fidelity.2.1.trans fullLorentzTriangularActual_connection_origin

/-! ## Same coherent actual: base simplicity and regenerated tangent -/

/-- Base simplicity at the common contact is read on the new coherent
actual itself.  It follows from exact generated zero-slice fidelity, not from
a stored constraint certificate. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_simplicity_origin :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravityAuxiliary
        0 =
      physicalIIPlusBivector
        (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
          0) := by
  have fidelity :=
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_initialSliceFidelity
      0
  rw [canonicalCauchySlicePoint_zero_zero] at fidelity
  rcases fidelity with
    ⟨coframeEq, _connectionEq, auxiliaryEq, _multiplierEq,
      _gaugeConnectionEq, _gaugeAuxiliaryEq, _scalarEq, _matterEq,
      _conjugateMatterEq⟩
  rw [auxiliaryEq, coframeEq]
  exact fullLorentzTriangularActual_simplicity_origin

/-- The regenerated `V(Ufinal)` is realized by genuine time derivatives of
the one coherent whole-domain actual.  This is the actual-level
`D R_simp(Ufinal)[V(Ufinal)] = 0` acceptance; no C3h200o tangent theorem is
used. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_canonicalOriginTangentSimplicity :
    CanonicalGravityOriginTangentSimplicity
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual := by
  have coframeOrigin :
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
          (canonicalCauchySlicePoint 0 0) =
        PreContorsionFullLorentzTriangularCurrent.coframe 0 := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent).coframe
          (canonicalCauchySlicePoint 0 0) = _
    rw [coherentDiagonalActual_coframe_slice,
      preContorsionFullLorentzTriangularCurrent_responseUpdate_zero]
  have coframeTangent :
      (fun internal coordinate =>
        deriv
            (fun time : Real =>
              positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
                (canonicalCauchySlicePoint time 0)
                internal coordinate)
            0) =
        (fun internal coordinate =>
          positiveP506MatterPreContorsionFullLorentzFreshResponse.coframe
            internal coordinate) := by
    funext internal coordinate
    change
      deriv
          (fun time : Real =>
            (currentCanonicalFullActionLorentzCoherentDiagonalActual
              positiveSmoothUnifiedSource
              PreContorsionFullLorentzTriangularCurrent).coframe
                (canonicalCauchySlicePoint time 0)
                internal coordinate)
          0 = _
    exact coherentDiagonalActual_coframe_originTangent
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0 internal coordinate
  unfold CanonicalGravityOriginTangentSimplicity
  rw [coframeOrigin, coframeTangent]
  funext internalPair spacetimePair
  change
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzCoherentDiagonalActual
            positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent).gravityAuxiliary
              (canonicalCauchySlicePoint time 0)
              internalPair spacetimePair)
        0 = _
  rw [coherentDiagonalActual_gravityAuxiliary_originTangent]
  exact congrFun
    (congrFun preContorsionFullLorentzFreshResponse_tangentSimplicity
      internalPair)
    spacetimePair

/-! ## C3h200r checkpoint law -/

structure PositiveP506MatterPreContorsionFullLorentzFreshCoherentActualLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos = 11
  primitiveSliceFidelity :
    PrimitiveSliceFidelity
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
  generatedFinalInitialSlice :
    PreContorsionFullLorentzFreshCoherentInitialSliceFidelity
  correctedConnectionPresent :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravityConnection
        0 =
      lorentzSkewConnectionOfBivectorOneForm
        preContorsionFullLorentzConnectionCorrection
  completeCanonicalContactResponse :
    StageNineCurrentCanonicalFullActionLorentzContactResponseLaw
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent 0
  simplicityBaseAcceptance :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravityAuxiliary
        0 =
      physicalIIPlusBivector
        (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
          0)
  regeneratedSimplicityTangent :
    CanonicalGravityOriginTangentSimplicity
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual

theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_realizes_C3h200r :
    PositiveP506MatterPreContorsionFullLorentzFreshCoherentActualLaw := by
  exact
    { exactP506L0Lineage :=
        positiveSmoothUnifiedSource_generates_exactP506L0Lineage
      endpointEleven := positiveSmoothUnifiedSource_generates_endpoint_eleven
      primitiveSliceFidelity :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_primitiveSliceFidelity
      generatedFinalInitialSlice :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_initialSliceFidelity
      correctedConnectionPresent :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_gravityConnection_origin
      completeCanonicalContactResponse :=
        preContorsionFullLorentzTriangularCurrent_contactResponse
      simplicityBaseAcceptance :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_simplicity_origin
      regeneratedSimplicityTangent :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_canonicalOriginTangentSimplicity }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
