import H0mework.Physics.ConstrainedCauchy.LocalActualLift
import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalActual

/-!
# Fixed P506/L0 KIN-16 full EC Cauchy successor

The KIN-16 primitive diagonal is one explicit smooth global actual.  This
module feeds that actual directly to the repaired-root full EC Cauchy write:

```text
fixed P506/L0 source
  + KIN-16 global actual
  -> action-generated twelve-row evolution write
  -> action-generated four-row constraint write
  -> one full-Cauchy successor actual.
```

The public constructor still consumes only `(source, current)`.  No target,
residual, response, branch, coefficient, equation, smoothness receipt, or
stationarity certificate is supplied here.  The resulting sixteen-row and
auxiliary balances are producer-soundness for those action writes; they are
not reclassified as independent constraints or as a continuous integral
curve.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality

noncomputable section

set_option autoImplicit false

/-- The first complete EC Cauchy successor of the fixed global KIN-16
actual.  Its two connection writes and live reaction are generated entirely
from the source and current actual. -/
def positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    positiveSmoothUnifiedSource
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual

/-- The full-Cauchy write preserves the already generated KIN-16 coframe
field exactly. -/
theorem fixedGlobalFullCauchy_coframe :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe _ _

/-- Both Cauchy legs preserve the source/action-generated Cartan origin
value. -/
theorem fixedGlobalFullCauchy_connection_origin :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.gravityConnection
        0 =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
        0 :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero _ _

/-- The preserved origin coframe is the fixed identity coframe. -/
theorem fixedGlobalFullCauchy_coframe_origin :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe
        0 = 1 := by
  rw [fixedGlobalFullCauchy_coframe]
  have zeroSlice :=
    congrArg
      (fun current : StageNineCauchyState => current.coframe 0)
      fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
        (canonicalCauchySlicePoint 0 0) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.coframe
        0 at zeroSlice
  have contactZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [contactZero,
    positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_coframe_one]
    at zeroSlice
  exact zeroSlice

/-- In particular the full-Cauchy successor remains nondegenerate at its
action contact.  No whole-base nondegeneracy claim is made here. -/
theorem fixedGlobalFullCauchy_coframe_origin_nondegenerate :
    Matrix.det
        (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe
          0) ≠ 0 := by
  rw [fixedGlobalFullCauchy_coframe_origin]
  norm_num

/-- Fixed-lineage regularity is consumed as a proved property of KIN-16;
the successor does not accept a smoothness certificate as source data. -/
theorem fixedGlobalFullCauchy_smooth :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.Smooth :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_smooth
    positiveSmoothUnifiedSource
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth

/-- The successor retains the computed `II+` carrier everywhere. -/
theorem fixedGlobalFullCauchy_simplicity :
    FormNativeGravitySimplicityEquation
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity _ _

/-- Its multiplier is recomputed from the live successor curvature rather
than transported from KIN-16. -/
theorem fixedGlobalFullCauchy_reactionSelfGenerated :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.gravitySimplicityMultiplier =
      formNativeGravityReactionField
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_reactionSelfGenerated _ _

/-- Recomputing that live reaction closes the full gravity-auxiliary
equation on the whole successor field. -/
theorem fixedGlobalFullCauchy_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation _ _

/-- The twelve evolution rows and four constraint rows are zero on one and
the same successor actual, with the load re-read after both writes. -/
theorem fixedGlobalFullCauchy_simultaneousBalance :
    (identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
            0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual) =
      0) ∧
    (identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
            0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual) =
      0) :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simultaneousBalance
    positiveSmoothUnifiedSource
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual

/-- Packing the generated twelve-plus-four split back through the faithful
coframe-coordinate basis yields the complete identity-contact EC covector.
This is one acceptance statement, not a second independent closure. -/
theorem fixedGlobalFullCauchy_EC_covector_zero :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
            0) +
        diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual =
      0 := by
  rcases fixedGlobalFullCauchy_simultaneousBalance with
    ⟨evolution, constraint⟩
  apply (coframeCovector_eq_iff_coordinateDirections _ _).2
  intro row column
  fin_cases column
  · have coordinate := congrFun constraint row
    simpa [identityDiracDualECConstraintObservation,
      identityECConstraintCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 0
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 1
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 2
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate

/-- The two Cauchy connection writes preserve all fields read by the Cartan
equation at the common origin.  The torsion--spin law is therefore re-read on
the successor actual itself, not retained as an opaque receipt. -/
theorem fixedGlobalFullCauchy_torsionSpin_origin :
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe
              0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt
                positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe
                0)
              (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.gravityConnection
                0))) =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus
              positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual)
            0) := by
  let input :=
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
  let output :=
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
  have contactZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  have inputClosure := fixedPrimitiveDiagonal_torsionSpin_zeroSlice 0
  rw [contactZero] at inputClosure
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource input output 0 rfl rfl rfl
  change
    formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus input) 0) =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus output) 0) at spinEq
  change
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (output.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt output.coframe 0)
              (output.gravityConnection 0))) =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus output) 0)
  calc
    _ =
        internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (input.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt input.coframe 0)
              (input.gravityConnection 0))) := by
      rw [show output.coframe = input.coframe by
        exact fixedGlobalFullCauchy_coframe,
        show output.gravityConnection 0 = input.gravityConnection 0 by
          exact fixedGlobalFullCauchy_connection_origin]
    _ =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus input) 0) :=
      inputClosure
    _ = _ := spinEq

/-- No-premise checkpoint: exact P506/L0 provenance, global regularity,
global simplicity and auxiliary closure, all sixteen identity-contact EC
rows, and the origin torsion--spin law belong to one source/action-generated
successor. -/
theorem fixedGlobalFullCauchy_realizes :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference /\
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.Smooth /\
      FormNativeGravitySimplicityEquation
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual /\
      FormNativeGravityAuxiliaryEquation
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual /\
      (internalBivectorDualThreeForm
            (torsionCoframeWedgeThreeForm
              (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe
                0)
              (pointwiseCartanTorsion
                (holonomicCoframeFirstJetAt
                  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe
                  0)
                (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.gravityConnection
                  0))) =
          formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
            (toContinuumPointField
              (restrictHolonomicConfigurationToIIPlus
                positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual)
              0)) /\
      identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature
              positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
              0) +
          diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual =
        0 := by
  exact
    ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      fixedGlobalFullCauchy_smooth,
      fixedGlobalFullCauchy_simplicity,
      fixedGlobalFullCauchy_auxiliaryEquation,
      fixedGlobalFullCauchy_torsionSpin_origin,
      fixedGlobalFullCauchy_EC_covector_zero⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
