import H0mework.Physics.ElectricEC.FixedGlobalDevelopmentMatterZeroSliceActionRead
import H0mework.Physics.FullOccurrence.FixedAssemblySeamClosure
import H0mework.Physics.FullOccurrence.FixedP286Verdict
import H0mework.Physics.DualVariation.RepairedMatterEquationReadout

/-!
# U6 primal Dirac zero-slice closure

The full-occurrence operator has already generated one global actual `U6`.
Its coframe, scalar, primal matter, and gauge connection are the corresponding
fields of `U5`; its Lorentz connection is the same-source Cartan restart of
that `U5`.  Consequently the complete primal action data of `U6` agrees with
the already generated Cartan current.

The fixed `U5` ambient first-jet theorem then supplies the primal Dirac law
on the whole zero slice.  The final theorem is a direct residual readout on
the same `U6`; no residual coordinate, support branch, target field, or
successor is an input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalPrimalZeroSliceClosure

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGlobalDevelopmentMatterZeroSliceActionRead
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev CartanCurrent : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source U5

private theorem u6_coframe_eq_cartan : U6.coframe = CartanCurrent.coframe := by
  calc
    U6.coframe = U5.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
        Source U5
    _ = CartanCurrent.coframe :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        Source U5).symm

private theorem u6_scalar_eq_cartan : U6.scalar = CartanCurrent.scalar := by
  calc
    U6.scalar = U5.scalar :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
        Source U5
    _ = CartanCurrent.scalar :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar
        Source U5).symm

private theorem u6_matter_eq_cartan : U6.matter = CartanCurrent.matter := by
  calc
    U6.matter = U5.matter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
        Source U5
    _ = CartanCurrent.matter :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
        Source U5).symm

private theorem u6_gravityConnection_eq_cartan :
    U6.gravityConnection = CartanCurrent.gravityConnection := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
      Source U5

private theorem u6_gaugeConnection_eq_cartan :
    U6.gaugeConnection = CartanCurrent.gaugeConnection := by
  calc
    U6.gaugeConnection = U5.gaugeConnection :=
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current
    _ = CartanCurrent.gaugeConnection :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
        Source U5).symm

private theorem u6_matterCovariantDerivative_eq_cartan
    (point : BasePoint) :
    holonomicMatterCovariantDerivative U6 point =
      holonomicMatterCovariantDerivative CartanCurrent point := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [u6_matter_eq_cartan, u6_gravityConnection_eq_cartan,
    u6_gaugeConnection_eq_cartan]

private theorem u6_knownVector_eq_cartan
    (point : BasePoint) :
    holonomicDiracDualCurrentCoframeMatterKnownVector U6 point =
      holonomicDiracDualCurrentCoframeMatterKnownVector CartanCurrent point := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [u6_coframe_eq_cartan, u6_scalar_eq_cartan, u6_matter_eq_cartan]
  simp_rw [u6_matterCovariantDerivative_eq_cartan]

/-- The generated full-occurrence actual satisfies the primal Dirac action
law at every occurrence of the fixed P506/L0 zero slice. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_primalActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw U6 point
      (holonomicMatterCovariantDerivative U6 point
        canonicalLorentzianTimeDirection) := by
  dsimp only
  have generated :=
    fixedP506L0CompleteJointLiveElectricECCartanRestart_primalActionLaw_zeroSlice
      space
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generated ⊢
  rw [congrFun u6_coframe_eq_cartan
      (canonicalCauchySlicePoint 0 space),
    u6_knownVector_eq_cartan,
    congrFun (u6_matterCovariantDerivative_eq_cartan
      (canonicalCauchySlicePoint 0 space))
      canonicalLorentzianTimeDirection]
  simpa [Source, U5, CartanCurrent] using generated

/-- The primal Dirac law reads out as an exact zero of the conjugate-matter
coordinate of the same `U6` joint residual on the complete zero slice. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source U6
      (canonicalCauchySlicePoint 0 space)).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source U6 direction
        (canonicalCauchySlicePoint 0 space) = 0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    Source U6 (canonicalCauchySlicePoint 0 space)
    (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_primalActionLaw_zeroSlice
      space)]
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalPrimalZeroSliceClosure
