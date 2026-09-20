import H0mework.Physics.GravityTail.FixedCompatibleRestart
import H0mework.Physics.SynchronizedJoint.FixedCoupledTemporalOriginProfileZero
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorMatterAdjointZeroSlice
import H0mework.Physics.ActualGerms.FixedJointMatterAdjointTemporalFirstJet
import H0mework.Physics.FixedJoint.FixedJointResidual
import H0mework.Physics.Coframe.CoframeNativeConjugateMatterFrameAction
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermSupport
import H0mework.Physics.Dirac.P286DiracAdjointCoefficientMaterial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fixed action-selected Dirac-current zero-slice and time-axis tangency

The fixed source/current action writer generates primal and adjoint temporal
velocities whose paired Dirac-vector-current rate vanishes on the complete
initial Cauchy slice.  The proof consumes the source-generated vacuum, the
actual Cartan connection, the fixed P286 representation, and the two live
action equations.  It accepts no rate, settlement, target, or adjoint
relation from the caller.

On the canonical time axis, the same fixed writer further reduces its full
carry tangency to the transverse primal/independent-adjoint first-jet rate.
No vanishing equation is assumed or claimed by that reduction.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedDiracVectorCurrentTemporalRateZeroSlice

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506ActionSelectedCoupledTemporalOriginProfileZero
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506CompleteJointMatterAdjointTemporalFirstJet
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailCompatibleRestart
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineConjugateMatterVariation
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineMatterActionTimeVelocity
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286DiracAdjointCoefficientMaterial
open StageNineLorentzConnectionVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorYukawaMassSpectrum
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory

open scoped ContDiff ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

noncomputable section

private abbrev Source := positiveSmoothUnifiedSource
private abbrev Current :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
private abbrev Carry :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current
private abbrev Coupled :=
  completeJointActionSelectedCoupledTemporalActual Source Current
private abbrev TailBase :=
  cartanECSynchronizedGravityTailBase Source Coupled
private abbrev Restart (point : BasePoint) :=
  completeJointGeneratedProfileRestartCurrent Source Carry point
private abbrev Primal (point : BasePoint) :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (Restart point)

private theorem carry_matter_zeroSlice (space : StageNineSpatialPoint) :
    Carry.matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  calc
    _ = Coupled.matter (canonicalCauchySlicePoint 0 space) :=
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        Source Carry space).symm
    _ = TailBase.matter (canonicalCauchySlicePoint 0 space) := by
      rfl
    _ = diracSpinTwoMatterProbe :=
      fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant space

private theorem carry_conjugateMatter_zeroSlice (space : StageNineSpatialPoint) :
    Carry.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  calc
    _ = Coupled.conjugateMatter (canonicalCauchySlicePoint 0 space) :=
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        Source Carry space).symm
    _ = TailBase.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
      rfl
    _ = diracSpinZeroMatterCoordinate :=
      fixedP506L0ActionSelectedGravityTailBase_conjugateMatter_zeroSlice_constant
        space

private theorem spatialDerivative_zero_of_zeroSlice_constant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E)
    (regular : ContDiff ℝ ∞ field)
    (value : E)
    (zeroSlice : ∀ space : StageNineSpatialPoint,
      field (canonicalCauchySlicePoint 0 space) = value)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative field
        (canonicalCauchySlicePoint 0 space) direction.succ = 0 := by
  have fieldDifferentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint 0 space) :=
    (regular.differentiable (by simp)).differentiableAt
  have sliceDerivative :=
    fieldDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  have sliceConstant :
      field ∘ canonicalCauchySlicePoint 0 =
        Function.const StageNineSpatialPoint value := by
    funext candidate
    exact zeroSlice candidate
  have sliceFderivZero :
      fderiv ℝ (field ∘ canonicalCauchySlicePoint 0) space = 0 := by
    rw [sliceConstant]
    simp
  rw [sliceDerivative.fderiv] at sliceFderivZero
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] E =>
      derivative (canonicalSpatialCoordinateDirection direction))
    sliceFderivZero
  unfold fieldDirectionalDerivative
  simpa [ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using applied

private theorem carry_matterCoordinates_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point))
        (canonicalCauchySlicePoint 0 space) direction.succ = 0 := by
  apply spatialDerivative_zero_of_zeroSlice_constant
      (fun point => matterCoordinateEquiv (Carry.matter point))
      actionSelectedCarry_matterCoordinates_contDiff
      (matterCoordinateEquiv diracSpinTwoMatterProbe)
  intro candidate
  exact congrArg matterCoordinateEquiv (carry_matter_zeroSlice candidate)

private theorem carry_conjugateMatterCoordinates_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry)
        (canonicalCauchySlicePoint 0 space) direction.succ = 0 := by
  apply spatialDerivative_zero_of_zeroSlice_constant
      (holonomicConjugateMatterCoordinates Carry)
      actionSelectedCarry_conjugateMatterCoordinates_contDiff
      (matterDualCoordinates diracSpinZeroMatterCoordinate)
  intro candidate
  exact congrArg matterDualCoordinates
    (carry_conjugateMatter_zeroSlice candidate)

private theorem restart_coframeFirstJet_identity
    (point : BasePoint) :
    holonomicCoframeFirstJetAt (Restart point).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_coframeFirstJet_origin,
    actionSelectedCarry_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

private theorem primal_coframeFirstJet_identity
    (point : BasePoint) :
    holonomicCoframeFirstJetAt (Primal point).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold Primal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe]
  exact restart_coframeFirstJet_identity point

private theorem restart_matter_origin_zeroSlice
    (space : StageNineSpatialPoint) :
    (Restart (canonicalCauchySlicePoint 0 space)).matter 0 =
      diracSpinTwoMatterProbe := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_matter_origin,
    carry_matter_zeroSlice]

private theorem restart_conjugateMatter_origin_zeroSlice
    (space : StageNineSpatialPoint) :
    (Restart (canonicalCauchySlicePoint 0 space)).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    fullyRecenterHolonomicConfiguration_conjugateMatter_origin,
    carry_conjugateMatter_zeroSlice]

private theorem primal_conjugateMatter_origin_zeroSlice
    (space : StageNineSpatialPoint) :
    (Primal (canonicalCauchySlicePoint 0 space)).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  unfold Primal actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [installMatterLinearTimeResponse_conjugateMatter,
    restart_conjugateMatter_origin_zeroSlice]

private theorem primal_gravityConnection_eq_restart (point : BasePoint) :
    (Primal point).gravityConnection = (Restart point).gravityConnection := by
  unfold Primal actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [installMatterLinearTimeResponse_gravityConnection]

private theorem primal_gaugeConnection_eq_restart (point : BasePoint) :
    (Primal point).gaugeConnection = (Restart point).gaugeConnection := by
  unfold Primal actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [installMatterLinearTimeResponse_gaugeConnection]

private theorem primal_scalar_eq_restart (point : BasePoint) :
    (Primal point).scalar = (Restart point).scalar := by
  exact
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_scalar
      (Restart point)

private theorem actionCartanConnectionAt_eq_of_jet_and_fields_at_two_points
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (jetEqual :
      holonomicCoframeFirstJetAt first.coframe firstPoint =
        holonomicCoframeFirstJetAt second.coframe secondPoint)
    (coframeEqual : first.coframe firstPoint = second.coframe secondPoint)
    (matterEqual : first.matter firstPoint = second.matter secondPoint)
    (conjugateEqual :
      first.conjugateMatter firstPoint =
        second.conjugateMatter secondPoint) :
    diracDualFormNativeActionCartanConnectionAt Source first firstPoint =
      diracDualFormNativeActionCartanConnectionAt Source second secondPoint := by
  have spinEqual :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
      Source first second firstPoint secondPoint coframeEqual matterEqual
        conjugateEqual
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [jetEqual, coframeEqual, spinEqual]

private theorem restart_gravityConnection_origin_zeroSlice_eq_positiveNormalForm
    (space : StageNineSpatialPoint) :
    (Restart (canonicalCauchySlicePoint 0 space)).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveDiracDualCartanContorsionNormalForm := by
  let Seed : StageNineHolonomicConfiguration :=
    cartanECSynchronizedGravityTailBase Source
      fixedP506L0CartanECConstraintCauchyGlobalActual
  have seedJet :
      holonomicCoframeFirstJetAt Seed.coframe
          (canonicalCauchySlicePoint 0 space) =
        identityCoframeMatterGeometry := by
    unfold Seed
    rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    apply coframeJet_eq_of_fields_eq
    · rfl
    · funext derivativeDirection internal coordinate
      simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]
  have connectionEq :
      (Restart (canonicalCauchySlicePoint 0 space)).gravityConnection 0 =
        fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection
          (canonicalCauchySlicePoint 0 space) := by
    unfold Restart completeJointGeneratedProfileRestartCurrent
      fixedSourceGeneratedCompatibleGravityTailBase
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
    apply actionCartanConnectionAt_eq_of_jet_and_fields_at_two_points
    · exact (restart_coframeFirstJet_identity
        (canonicalCauchySlicePoint 0 space)).trans seedJet.symm
    · calc
        (fullyRecenterHolonomicConfiguration Carry
            (canonicalCauchySlicePoint 0 space)).coframe 0 = 1 := by
              rw [fullyRecenterHolonomicConfiguration_coframe_origin,
                actionSelectedCarry_coframe_eq_one]
        _ = Seed.coframe (canonicalCauchySlicePoint 0 space) := by
          unfold Seed
          rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    · calc
        (fullyRecenterHolonomicConfiguration Carry
            (canonicalCauchySlicePoint 0 space)).matter 0 =
            diracSpinTwoMatterProbe := by
              rw [fullyRecenterHolonomicConfiguration_matter_origin,
                carry_matter_zeroSlice]
        _ = Seed.matter (canonicalCauchySlicePoint 0 space) := by
          unfold Seed
          exact
            (fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant
              space).symm
    · calc
        (fullyRecenterHolonomicConfiguration Carry
            (canonicalCauchySlicePoint 0 space)).conjugateMatter 0 =
            diracSpinZeroMatterCoordinate := by
              rw [fullyRecenterHolonomicConfiguration_conjugateMatter_origin,
                carry_conjugateMatter_zeroSlice]
        _ = Seed.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
          unfold Seed
          exact
            (fixedP506L0ActionSelectedGravityTailBase_conjugateMatter_zeroSlice_constant
              space).symm
  rw [connectionEq,
    fixedGravityTailCompatibleBase_connection_zeroSlice_eq_positiveNormalForm]

private theorem restart_scalar_origin_zeroSlice_eq_vacuum
    (space : StageNineSpatialPoint) :
    (Restart (canonicalCauchySlicePoint 0 space)).scalar 0 =
      sourceGeneratedVacuumCoordinates Source := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    fullyRecenterHolonomicConfiguration_scalar_origin,
    congrFun actionSelectedCarry_scalar_eq_u6RadialQuarticCarry,
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_normalForm]
  simp

private theorem p286_probe_action_eigenvalue_re_zero
    (data : P286LieBlockData) :
    ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + data.2.2.1).re = 0 := by
  have colorStar := congrArg
    (fun matrix : Matrix (Fin 3) (Fin 3) ℂ => matrix 0 0)
    (specialUnitaryLieMatrix_star data.1)
  change conj ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0) =
    -((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0) at colorStar
  have colorRe := congrArg Complex.re colorStar
  simp only [Complex.conj_re, Complex.neg_re] at colorRe
  have colorDiagonalRe :
      ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0).re = 0 := by
    linarith
  have hyperRe : (data.2.2 : ℂ).re = 0 :=
    StageNineHyperchargeAuxiliaryVariation.hypercharge_real_part_eq_zero
      data.2.2
  rw [Complex.add_re, colorDiagonalRe, hyperRe, zero_add]

private theorem restart_matterCoordinates_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((Restart (canonicalCauchySlicePoint 0 space)).matter localPoint))
        0 direction.succ = 0 := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  change
    fieldDirectionalDerivative
        ((fun point => matterCoordinateEquiv (Carry.matter point)) ∘
          canonicalSpacetimeContactTranslation
            (canonicalCauchySlicePoint 0 space))
        0 direction.succ = 0
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simpa only [canonicalSpacetimeContactTranslation_zero] using
    carry_matterCoordinates_spatialDerivative_zeroSlice space direction

private theorem primal_conjugateMatterCoordinates_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          (Primal (canonicalCauchySlicePoint 0 space)))
        0 direction.succ = 0 := by
  unfold Primal actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  unfold holonomicConjugateMatterCoordinates
  rw [installMatterLinearTimeResponse_conjugateMatter]
  change
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          (Restart (canonicalCauchySlicePoint 0 space)))
        0 direction.succ = 0
  unfold holonomicConjugateMatterCoordinates Restart
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  change
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry ∘
          canonicalSpacetimeContactTranslation
            (canonicalCauchySlicePoint 0 space))
        0 direction.succ = 0
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simpa only [canonicalSpacetimeContactTranslation_zero] using
    carry_conjugateMatterCoordinates_spatialDerivative_zeroSlice space direction

private theorem primal_conjugateMatterDerivativeDual_spatial_zeroSlice
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    holonomicConjugateMatterDerivativeDual
        (Primal (canonicalCauchySlicePoint 0 space)) 0 direction.succ = 0 := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  rw [primal_conjugateMatterCoordinates_spatialDerivative_zeroSlice]
  simp

/-- Exact fixed-zero-slice inventory of the restart that generates the
action-selected complete-joint profile.  This packages only source-generated
fields already used by the Dirac-current consumer; it supplies no velocity,
action law, target, or settlement witness. -/
theorem fixedActionSelectedZeroSliceProfileRestartCore
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    let restart := completeJointGeneratedProfileRestartCurrent
      positiveSmoothUnifiedSource
      (completeJointActionSelectedScalarMomentumCarryActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
      point
    holonomicCoframeFirstJetAt restart.coframe 0 =
        identityCoframeMatterGeometry ∧
      restart.matter 0 = diracSpinTwoMatterProbe ∧
      restart.scalar 0 =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource ∧
      restart.gravityConnection 0 =
        lorentzSkewConnectionOfBivectorOneForm
          positiveDiracDualCartanContorsionNormalForm ∧
      ∀ direction : Fin 3,
        fieldDirectionalDerivative
            (fun localPoint =>
              matterCoordinateEquiv (restart.matter localPoint))
            0 direction.succ = 0 := by
  dsimp only
  exact
    ⟨restart_coframeFirstJet_identity
        (canonicalCauchySlicePoint 0 space),
      restart_matter_origin_zeroSlice space,
      restart_scalar_origin_zeroSlice_eq_vacuum space,
      restart_gravityConnection_origin_zeroSlice_eq_positiveNormalForm space,
      restart_matterCoordinates_spatialDerivative_zeroSlice space⟩

/-- The fixed primal/adjoint action writer is tangent to all four real
Dirac-vector-current coordinates on the complete initial Cauchy slice. -/
theorem fixedActionSelectedDiracVectorCurrentTemporalRate_zeroSlice :
    ∀ direction space,
      let point := canonicalCauchySlicePoint 0 space
      let Carry := completeJointActionSelectedScalarMomentumCarryActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
      let Coupled := completeJointActionSelectedCoupledTemporalActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
      let profile := sourceActionGeneratedDiracDualCompleteJointProfiles
        positiveSmoothUnifiedSource Carry point
      (profile.adjointVelocity
          (diracMatrixMatterAction (diracGamma direction) (Coupled.matter point)) +
        Coupled.conjugateMatter point
          (diracMatrixMatterAction (diracGamma direction) profile.matterVelocity)).im = 0 := by
  intro direction space
  dsimp only
  rw [completeJointActionSelectedCoupledTemporalActual,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice,
    carry_matter_zeroSlice, carry_conjugateMatter_zeroSlice]
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
  have restartJet := restart_coframeFirstJet_identity
    (canonicalCauchySlicePoint 0 space)
  have primalJet := primal_coframeFirstJet_identity
    (canonicalCauchySlicePoint 0 space)
  rw [holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
    _ _ primalJet]
  unfold
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeConjugateMatterSpatialTransport
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [coframe_eq_one_of_identity_firstJet _ _ restartJet]
  rw [primal_conjugateMatter_origin_zeroSlice]
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterCovariantDerivative holonomicMatterConnectionAction
    holonomicIdentityCoframeMatterConnectionOperator
  rw [congrFun (primal_gravityConnection_eq_restart _) 0,
    congrFun (primal_gaugeConnection_eq_restart _) 0,
    congrFun (primal_scalar_eq_restart _) 0]
  rw [restart_matter_origin_zeroSlice]
  rw [restart_gravityConnection_origin_zeroSlice_eq_positiveNormalForm]
  rw [restart_scalar_origin_zeroSlice_eq_vacuum]
  rw [show scalarCoordinateEquiv.symm
      (sourceGeneratedVacuumCoordinates Source) =
        sourceGeneratedVacuumBase Source by
    simp [sourceGeneratedVacuumCoordinates]]
  rw [
    StageNineDiracDualFormNativeFixedP506JointResidual.fixedP506VacuumDiracDualYukawa_spinTwo_zero]
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.sum_apply,
    map_add, map_sub, map_smul]
  simp_rw [
    StageNineDiracDualFormNativeFixedP506JointResidual.fixedDiracSpinZeroMatterCoordinate_diracDualRightChiralYukawa_zero]
  simp_rw [primal_conjugateMatterDerivativeDual_spatial_zeroSlice,
    restart_matterCoordinates_spatialDerivative_zeroSlice]
  rw [coframe_eq_one_of_identity_firstJet _ _ restartJet]
  simp_rw [currentCoframeMatterTemporalPrincipalInverse_one]
  rw [Fin.sum_univ_three]
  fin_cases direction <;>
    simp [
      canonicalLorentzianTimeDirection,
      PointwiseDiracSpinConnectionLift.diracSpinConnectionLift,
      StageNineLorentzConnectionVariation.loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      diracExteriorMotherLieAction, internalMatterLinearAction,
      exteriorSpinorMotherLieAction,
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.occupiedExteriorAction_coordinate,
      StageNineMatterActionTimeVelocity.identityCoframeMatterTimePrincipal,
      diracMatrixMatterAction, diracSpinZeroMatterCoordinate,
      hyperchargeDegreeTwoMatterCoordinate,
      diracSpinTwoMatterProbe,
      SU7ExteriorMatterGaugeCovariantJet.p286HyperchargeMatterProbe,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      inverseCoframeDiracGamma_identity,
      Fin.sum_univ_six, Fin.sum_univ_four,
      Fin.sum_univ_three,
      PointwiseDiracSpinConnectionLift.lorentzBivectorFirst,
      PointwiseDiracSpinConnectionLift.lorentzBivectorSecond,
      positiveDiracDualCartanContorsionNormalForm,
      show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
        PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl]
  all_goals
    have gaugeRe (gaugeDirection : LorentzianIndex) :
        ((((Restart (canonicalCauchySlicePoint 0 space)).gaugeConnection
              0 gaugeDirection).1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0).re +
            (((Restart (canonicalCauchySlicePoint 0 space)).gaugeConnection
              0 gaugeDirection).2.2 : ℂ).re = 0 := by
      simpa only [Complex.add_re] using
        p286_probe_action_eigenvalue_re_zero
          ((Restart (canonicalCauchySlicePoint 0 space)).gaugeConnection
            0 gaugeDirection)
    dsimp only [Restart] at gaugeRe ⊢
    linarith [gaugeRe 0, gaugeRe 1, gaugeRe 2, gaugeRe 3]

private theorem carry_matter_timeAxis_constant (time : ℝ) :
    Carry.matter
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
      diracSpinTwoMatterProbe := by
  apply matterCoordinateEquiv.injective
  change matterCoordinateEquiv
      (fixedP506L0CompleteJointActionSpacetimeSectionActual.matter
        (canonicalCauchySlicePoint time 0)) = _
  rw [fixedP506L0CompleteJointActionSpacetimeSection_matter_normalForm]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]
  rw [(fixedP506JointActual_matterAdjoint_canonicalVelocityDrift_normalForm
    time 0).1]
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  have writes :=
    fixedP506L0CartanRestartActual_origin_primalAdjointTimeResponseWrites_zero
  rw [writes.1]
  simp

private theorem carry_conjugateMatter_timeAxis_constant (time : ℝ) :
    Carry.conjugateMatter
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
      diracSpinZeroMatterCoordinate := by
  apply LinearMap.ext
  intro matter
  change
    fixedP506L0CompleteJointActionSpacetimeSectionActual.conjugateMatter
        (canonicalCauchySlicePoint time 0) matter = _
  rw [fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_field_normalForm]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [(fixedP506JointActual_matterAdjoint_canonicalVelocityDrift_normalForm
    time 0).2 matter]
  have writes :=
    fixedP506L0CartanRestartActual_origin_primalAdjointTimeResponseWrites_zero
  rw [writes.2]
  simp

/-- The fixed action-selected carry is source-constant in its primal matter
field along the canonical time axis, hence its actual temporal derivative is
zero there. -/
theorem fixedActionSelectedCarry_matterTemporalDerivative_timeAxis_zero
    (time : ℝ) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point))
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        canonicalLorentzianTimeDirection = 0 := by
  have actual := field_timeLine_hasDerivAt
    (fun point => matterCoordinateEquiv (Carry.matter point))
    (0 : StageNineSpatialPoint) time
    (actionSelectedCarry_matterCoordinates_contDiff.differentiable
      (by simp) |>.differentiableAt)
  have zeroDerivative : HasDerivAt
      (fun candidateTime => matterCoordinateEquiv
        (Carry.matter
          (canonicalCauchySlicePoint candidateTime 0))) 0 time := by
    rw [show
      (fun candidateTime => matterCoordinateEquiv
        (Carry.matter
          (canonicalCauchySlicePoint candidateTime 0))) =
      fun _ : ℝ => matterCoordinateEquiv diracSpinTwoMatterProbe by
        funext candidateTime
        rw [carry_matter_timeAxis_constant]]
    exact hasDerivAt_const (x := time) _
  exact actual.unique zeroDerivative

/-- The independently generated adjoint carry is likewise source-constant
on the same canonical time axis. -/
theorem fixedActionSelectedCarry_adjointTemporalDerivative_timeAxis_zero
    (time : ℝ) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry)
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        canonicalLorentzianTimeDirection = 0 := by
  have actual := field_timeLine_hasDerivAt
    (holonomicConjugateMatterCoordinates Carry)
    (0 : StageNineSpatialPoint) time
    (actionSelectedCarry_conjugateMatterCoordinates_contDiff.differentiable
      (by simp) |>.differentiableAt)
  have zeroDerivative : HasDerivAt
      (fun candidateTime =>
        holonomicConjugateMatterCoordinates Carry
          (canonicalCauchySlicePoint candidateTime 0)) 0 time := by
    rw [show
      (fun candidateTime =>
        holonomicConjugateMatterCoordinates Carry
          (canonicalCauchySlicePoint candidateTime 0)) =
      fun _ : ℝ => matterDualCoordinates diracSpinZeroMatterCoordinate by
        funext candidateTime
        unfold holonomicConjugateMatterCoordinates
        rw [carry_conjugateMatter_timeAxis_constant]]
    exact hasDerivAt_const (x := time) _
  exact actual.unique zeroDerivative

private theorem restart_matter_origin_timeAxis (time : ℝ) :
    (Restart (canonicalCauchySlicePoint time 0)).matter 0 =
      diracSpinTwoMatterProbe := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_matter_origin,
    carry_matter_timeAxis_constant]

private theorem restart_conjugateMatter_origin_timeAxis (time : ℝ) :
    (Restart (canonicalCauchySlicePoint time 0)).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    fullyRecenterHolonomicConfiguration_conjugateMatter_origin,
    carry_conjugateMatter_timeAxis_constant]

private theorem primal_conjugateMatter_origin_timeAxis (time : ℝ) :
    (Primal (canonicalCauchySlicePoint time 0)).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  unfold Primal actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [installMatterLinearTimeResponse_conjugateMatter,
    restart_conjugateMatter_origin_timeAxis]

private theorem carry_scalar_timeAxis_vacuum (time : ℝ) :
    Carry.scalar (canonicalCauchySlicePoint time 0) =
      sourceGeneratedVacuumCoordinates Source := by
  rw [congrFun actionSelectedCarry_scalar_eq_u6RadialQuarticCarry]
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_normalForm]
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  have radialZero :
      p286RadialQuarticTemporalConnection
          fixedP506L0U6OccurrenceP286MotherActionCharge
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) = 0 := by
    funext direction
    simp [p286RadialQuarticTemporalConnection,
      p286SpatialRadialQuarticCoefficient, p286SpatialRadiusSquared,
      p286SpatialMetricCovectorOperator, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  rw [radialZero]
  simp

private theorem restart_scalar_origin_timeAxis_eq_vacuum (time : ℝ) :
    (Restart (canonicalCauchySlicePoint time 0)).scalar 0 =
      sourceGeneratedVacuumCoordinates Source := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    fullyRecenterHolonomicConfiguration_scalar_origin,
    carry_scalar_timeAxis_vacuum]

private theorem restart_gravityConnection_origin_timeAxis_eq_positiveNormalForm
    (time : ℝ) :
    (Restart (canonicalCauchySlicePoint time 0)).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveDiracDualCartanContorsionNormalForm := by
  let Seed : StageNineHolonomicConfiguration :=
    cartanECSynchronizedGravityTailBase Source
      fixedP506L0CartanECConstraintCauchyGlobalActual
  have seedJet :
      holonomicCoframeFirstJetAt Seed.coframe
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) =
        identityCoframeMatterGeometry := by
    unfold Seed
    rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    apply coframeJet_eq_of_fields_eq
    · rfl
    · funext derivativeDirection internal coordinate
      simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]
  have connectionEq :
      (Restart (canonicalCauchySlicePoint time 0)).gravityConnection 0 =
        fixedSourceGeneratedCompatibleGravityTailBase.gravityConnection
          (canonicalCauchySlicePoint 0 0) := by
    unfold Restart completeJointGeneratedProfileRestartCurrent
      fixedSourceGeneratedCompatibleGravityTailBase
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
    apply actionCartanConnectionAt_eq_of_jet_and_fields_at_two_points
    · exact (restart_coframeFirstJet_identity
        (canonicalCauchySlicePoint time 0)).trans seedJet.symm
    · calc
        (fullyRecenterHolonomicConfiguration Carry
            (canonicalCauchySlicePoint time 0)).coframe 0 = 1 := by
              rw [fullyRecenterHolonomicConfiguration_coframe_origin,
                actionSelectedCarry_coframe_eq_one]
        _ = Seed.coframe (canonicalCauchySlicePoint 0 0) := by
          unfold Seed
          rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    · calc
        (fullyRecenterHolonomicConfiguration Carry
            (canonicalCauchySlicePoint time 0)).matter 0 =
            diracSpinTwoMatterProbe := by
              rw [fullyRecenterHolonomicConfiguration_matter_origin,
                carry_matter_timeAxis_constant]
        _ = Seed.matter (canonicalCauchySlicePoint 0 0) := by
          unfold Seed
          exact
            (fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant
              0).symm
    · calc
        (fullyRecenterHolonomicConfiguration Carry
            (canonicalCauchySlicePoint time 0)).conjugateMatter 0 =
            diracSpinZeroMatterCoordinate := by
              rw [fullyRecenterHolonomicConfiguration_conjugateMatter_origin,
                carry_conjugateMatter_timeAxis_constant]
        _ = Seed.conjugateMatter (canonicalCauchySlicePoint 0 0) := by
          unfold Seed
          exact
            (fixedP506L0ActionSelectedGravityTailBase_conjugateMatter_zeroSlice_constant
              0).symm
  rw [connectionEq,
    fixedGravityTailCompatibleBase_connection_zeroSlice_eq_positiveNormalForm]

private theorem restart_matterCoordinates_spatialDerivative_timeAxis
    (time : ℝ) (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((Restart (canonicalCauchySlicePoint time 0)).matter localPoint))
        0 direction.succ =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point))
        (canonicalCauchySlicePoint time 0) direction.succ := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  change
    fieldDirectionalDerivative
        ((fun point => matterCoordinateEquiv (Carry.matter point)) ∘
          canonicalSpacetimeContactTranslation
            (canonicalCauchySlicePoint time 0))
        0 direction.succ = _
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simp only [canonicalSpacetimeContactTranslation_zero]

private theorem primal_conjugateMatterCoordinates_spatialDerivative_timeAxis
    (time : ℝ) (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          (Primal (canonicalCauchySlicePoint time 0)))
        0 direction.succ =
      fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry)
        (canonicalCauchySlicePoint time 0) direction.succ := by
  unfold Primal actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  unfold holonomicConjugateMatterCoordinates
  rw [installMatterLinearTimeResponse_conjugateMatter]
  change
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          (Restart (canonicalCauchySlicePoint time 0)))
        0 direction.succ = _
  unfold holonomicConjugateMatterCoordinates Restart
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  change
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry ∘
          canonicalSpacetimeContactTranslation
            (canonicalCauchySlicePoint time 0))
        0 direction.succ = _
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simp only [canonicalSpacetimeContactTranslation_zero]
  rfl

private theorem primal_conjugateMatterDerivativeDual_spatial_timeAxis
    (time : ℝ) (direction : Fin 3) :
    holonomicConjugateMatterDerivativeDual
        (Primal (canonicalCauchySlicePoint time 0)) 0 direction.succ =
      matterDualOfCoordinates
        (fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates Carry)
          (canonicalCauchySlicePoint time 0) direction.succ) := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  rw [primal_conjugateMatterCoordinates_spatialDerivative_timeAxis]

/-! ## Exact affine reduction of the remaining transverse rate -/

private def timeAxisPrimalSpatialRateCoordinates
    (space : StageNineSpatialPoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
      (actionGeneratedMatterRawTimeVelocity
        positiveP506MatterCurrentFullSynchronizedCauchyState space) -
    matterCoordinateEquiv
      (actionGeneratedMatterRawTimeVelocity
        positiveP506MatterCurrentFullSynchronizedCauchyState 0) +
    matterCoordinateEquiv
      (diracDualCurrentCoframeMatterTimeResponseWrite
        (fixedP506L0CartanRestartActual space))

private def timeAxisAdjointSpatialRateCoordinates
    (space : StageNineSpatialPoint) : MatterCoordinateCarrier :=
  matterDualCoordinates
      (actionGeneratedConjugateMatterTimeDerivative
        positiveP506MatterCurrentFullSynchronizedCauchyState space) -
    matterDualCoordinates
      (actionGeneratedConjugateMatterTimeDerivative
        positiveP506MatterCurrentFullSynchronizedCauchyState 0) +
    matterDualCoordinates
      (liveCoframeConjugateMatterTimeResponseWrite
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space)))

private theorem carry_matter_slice_affine_normalForm
    (time : ℝ) (space : StageNineSpatialPoint) :
    matterCoordinateEquiv
        (Carry.matter (canonicalCauchySlicePoint time space)) =
      matterCoordinateEquiv diracSpinTwoMatterProbe +
        time • timeAxisPrimalSpatialRateCoordinates space := by
  change matterCoordinateEquiv
      (fixedP506L0CompleteJointActionSpacetimeSectionActual.matter
        (canonicalCauchySlicePoint time space)) = _
  rw [fixedP506L0CompleteJointActionSpacetimeSection_matter_normalForm]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]
  rw [(fixedP506JointActual_matterAdjoint_canonicalVelocityDrift_normalForm
    time space).1]
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  unfold timeAxisPrimalSpatialRateCoordinates
  rw [smul_add]
  module

private theorem timeAxisPrimalSpatialRateCoordinates_contDiff :
    ContDiff ℝ ∞ timeAxisPrimalSpatialRateCoordinates := by
  exact
    (fixedMatterRawVelocity_coordinates_contDiff.sub contDiff_const).add
      fixedP506L0CompleteJointMatterResponseWrite_contDiff

private theorem carry_conjugateMatter_slice_affine_normalForm
    (time : ℝ) (space : StageNineSpatialPoint) :
    holonomicConjugateMatterCoordinates Carry
        (canonicalCauchySlicePoint time space) =
      matterDualCoordinates diracSpinZeroMatterCoordinate +
        time • timeAxisAdjointSpatialRateCoordinates space := by
  unfold holonomicConjugateMatterCoordinates
  change matterDualCoordinates
      (fixedP506L0CompleteJointActionSpacetimeSectionActual.conjugateMatter
        (canonicalCauchySlicePoint time space)) = _
  rw [
    fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_field_normalForm]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  have drift :
      FixedP506JointActual.conjugateMatter
          (canonicalCauchySlicePoint time space) =
        diracSpinZeroMatterCoordinate +
          time •
            (actionGeneratedConjugateMatterTimeDerivative
                positiveP506MatterCurrentFullSynchronizedCauchyState space -
              actionGeneratedConjugateMatterTimeDerivative
                positiveP506MatterCurrentFullSynchronizedCauchyState 0) := by
    apply LinearMap.ext
    intro matter
    simpa only [LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sub_apply] using
      (fixedP506JointActual_matterAdjoint_canonicalVelocityDrift_normalForm
        time space).2 matter
  rw [drift]
  apply PiLp.ext
  intro index
  simp [matterDualCoordinates, timeAxisAdjointSpatialRateCoordinates]
  module

private theorem timeAxisAdjointSpatialRateCoordinates_contDiff :
    ContDiff ℝ ∞ timeAxisAdjointSpatialRateCoordinates := by
  rw [show timeAxisAdjointSpatialRateCoordinates =
      fun space =>
        holonomicConjugateMatterCoordinates Carry
            (canonicalCauchySlicePoint 1 space) -
          matterDualCoordinates diracSpinZeroMatterCoordinate by
    funext space
    rw [carry_conjugateMatter_slice_affine_normalForm]
    simp]
  exact
    (actionSelectedCarry_conjugateMatterCoordinates_contDiff.comp
      (by
        rw [show canonicalCauchySlicePoint 1 =
            fun space =>
              EuclideanSpace.single canonicalLorentzianTimeDirection 1 +
                canonicalSpatialInclusion space by
          funext space
          exact canonicalCauchySlicePoint_eq_const_add_inclusion 1 space]
        exact contDiff_const.add canonicalSpatialInclusion.contDiff)).sub
      contDiff_const

private theorem carry_matter_spatialDerivative_timeAxis_affine
    (time : ℝ) (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point))
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        direction.succ =
      time •
        fderiv ℝ timeAxisPrimalSpatialRateCoordinates 0
          (canonicalSpatialCoordinateDirection direction) := by
  let field : BasePoint → MatterCoordinateCarrier :=
    fun point => matterCoordinateEquiv (Carry.matter point)
  have fieldDifferentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) :=
    actionSelectedCarry_matterCoordinates_contDiff
      |>.differentiable (by simp) |>.differentiableAt
  rw [← fderiv_canonicalCauchySlicePoint_spatial_local
    field time 0 direction fieldDifferentiable]
  have sliceEq :
      field ∘ canonicalCauchySlicePoint time =
        fun space => matterCoordinateEquiv diracSpinTwoMatterProbe +
          time • timeAxisPrimalSpatialRateCoordinates space := by
    funext space
    exact carry_matter_slice_affine_normalForm time space
  rw [sliceEq]
  have rateHasFDerivAt :
      HasFDerivAt timeAxisPrimalSpatialRateCoordinates
        (fderiv ℝ timeAxisPrimalSpatialRateCoordinates 0) 0 :=
    timeAxisPrimalSpatialRateCoordinates_contDiff.differentiable
      (by simp) |>.differentiableAt.hasFDerivAt
  have totalHasFDerivAt :=
    (hasFDerivAt_const (x := (0 : StageNineSpatialPoint))
      (matterCoordinateEquiv diracSpinTwoMatterProbe)).add
      (rateHasFDerivAt.const_smul time)
  change
    (fderiv ℝ
      ((fun _ : StageNineSpatialPoint =>
          matterCoordinateEquiv diracSpinTwoMatterProbe) +
        time • timeAxisPrimalSpatialRateCoordinates) 0)
        (canonicalSpatialCoordinateDirection direction) = _
  rw [totalHasFDerivAt.fderiv]
  simp

private theorem carry_adjoint_spatialDerivative_timeAxis_affine
    (time : ℝ) (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry)
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        direction.succ =
      time •
        fderiv ℝ timeAxisAdjointSpatialRateCoordinates 0
          (canonicalSpatialCoordinateDirection direction) := by
  let field : BasePoint → MatterCoordinateCarrier :=
    holonomicConjugateMatterCoordinates Carry
  have fieldDifferentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) :=
    actionSelectedCarry_conjugateMatterCoordinates_contDiff
      |>.differentiable (by simp) |>.differentiableAt
  rw [← fderiv_canonicalCauchySlicePoint_spatial_local
    field time 0 direction fieldDifferentiable]
  have sliceEq :
      field ∘ canonicalCauchySlicePoint time =
        fun space => matterDualCoordinates diracSpinZeroMatterCoordinate +
          time • timeAxisAdjointSpatialRateCoordinates space := by
    funext space
    exact carry_conjugateMatter_slice_affine_normalForm time space
  rw [sliceEq]
  have rateHasFDerivAt :
      HasFDerivAt timeAxisAdjointSpatialRateCoordinates
        (fderiv ℝ timeAxisAdjointSpatialRateCoordinates 0) 0 :=
    timeAxisAdjointSpatialRateCoordinates_contDiff.differentiable
      (by simp) |>.differentiableAt.hasFDerivAt
  have totalHasFDerivAt :=
    (hasFDerivAt_const (x := (0 : StageNineSpatialPoint))
      (matterDualCoordinates diracSpinZeroMatterCoordinate)).add
      (rateHasFDerivAt.const_smul time)
  change
    (fderiv ℝ
      ((fun _ : StageNineSpatialPoint =>
          matterDualCoordinates diracSpinZeroMatterCoordinate) +
        time • timeAxisAdjointSpatialRateCoordinates) 0)
        (canonicalSpatialCoordinateDirection direction) = _
  rw [totalHasFDerivAt.fderiv]
  simp

private theorem identityCoframeMatterPrincipal_real_smul_local
    (direction : LorentzianIndex) (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    identityCoframeMatterPrincipal direction (parameter • matter) =
      parameter • identityCoframeMatterPrincipal direction matter := by
  exact
    (identityCoframeMatterPrincipal direction).map_smul_of_tower
      parameter matter

private theorem actionGeneratedTemporalDerivative_one_real_smul
    (parameter : ℝ) (knownVector : DiracExteriorMatterCarrier) :
    actionGeneratedCurrentCoframeMatterTemporalDerivative 1
        (parameter • knownVector) =
      parameter •
        actionGeneratedCurrentCoframeMatterTemporalDerivative 1
          knownVector := by
  unfold actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [(currentCoframeMatterTemporalPrincipalInverse 1).map_smul_of_tower]
  module

private theorem diracMatrixMatterAction_real_smul_local
    (matrix : DiracMatrix) (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction matrix (parameter • matter) =
      parameter • diracMatrixMatterAction matrix matter := by
  exact (diracMatrixMatterAction matrix).map_smul_of_tower parameter matter

private theorem diracSpinZeroMatterCoordinate_real_smul_local
    (parameter : ℝ) (matter : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate (parameter • matter) =
      parameter • diracSpinZeroMatterCoordinate matter := by
  exact diracSpinZeroMatterCoordinate.map_smul_of_tower parameter matter

/-- The exact transverse primal/adjoint current-rate term generated by the
fixed action-selected carry on the canonical time axis.  It reads only the
spatial first jets of that fixed carry; it is neither a target equation nor a
settlement receipt. -/
def fixedActionSelectedTimeAxisTransverseDiracCurrentRate
    (direction : LorentzianIndex) (time : ℝ) : ℝ :=
  let point := canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)
  let primalSpatialKnown : DiracExteriorMatterCarrier :=
    ∑ axis : Fin 3,
      identityCoframeMatterPrincipal axis.succ
        (matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
            point axis.succ))
  let adjointSpatialTransport :
      Module.Dual ℂ DiracExteriorMatterCarrier :=
    ∑ axis : Fin 3,
      (matterDualOfCoordinates
          (fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates Carry) point axis.succ)).comp
        (identityCoframeMatterPrincipal axis.succ)
  (((-adjointSpatialTransport).comp
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection))
      (diracMatrixMatterAction (diracGamma direction)
        diracSpinTwoMatterProbe) +
    diracSpinZeroMatterCoordinate
      (diracMatrixMatterAction (diracGamma direction)
        (actionGeneratedCurrentCoframeMatterTemporalDerivative 1
          primalSpatialKnown))).im

/-- The remaining transverse rate has one fixed coefficient: the exact
affine matter/adjoint spatial jets make its value at arbitrary canonical time
equal to `time` times its source-owned unit-time value.  Thus no all-time
equation is hidden in this reduction; the next producer must settle that one
fixed coefficient together with the temporal-primitive cross term. -/
theorem fixedActionSelectedTimeAxisTransverseDiracCurrentRate_eq_time_mul_unit
    (direction : LorentzianIndex) (time : ℝ) :
    fixedActionSelectedTimeAxisTransverseDiracCurrentRate direction time =
      time *
        fixedActionSelectedTimeAxisTransverseDiracCurrentRate direction 1 := by
  unfold fixedActionSelectedTimeAxisTransverseDiracCurrentRate
  dsimp only
  simp_rw [carry_matter_spatialDerivative_timeAxis_affine,
    carry_adjoint_spatialDerivative_timeAxis_affine]
  simp_rw [one_smul]
  simp_rw [matterDualOfCoordinates_real_smul,
    matterCoordinateEquiv_symm_real_smul]
  simp_rw [identityCoframeMatterPrincipal_real_smul_local]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.neg_apply]
  have primalSum :
      (∑ axis : Fin 3,
        time • identityCoframeMatterPrincipal axis.succ
          (matterCoordinateEquiv.symm
            ((fderiv ℝ timeAxisPrimalSpatialRateCoordinates 0)
              (canonicalSpatialCoordinateDirection axis)))) =
        time • ∑ axis : Fin 3,
          identityCoframeMatterPrincipal axis.succ
            (matterCoordinateEquiv.symm
              ((fderiv ℝ timeAxisPrimalSpatialRateCoordinates 0)
                (canonicalSpatialCoordinateDirection axis))) := by
    simp_rw [Fin.sum_univ_three]
    module
  rw [primalSum]
  simp_rw [actionGeneratedTemporalDerivative_one_real_smul,
    diracMatrixMatterAction_real_smul_local,
    diracSpinZeroMatterCoordinate_real_smul_local]
  simp only [LinearMap.smul_apply, Complex.real_smul,
    Complex.add_im, Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  simp_rw [Fin.sum_univ_three]
  have ofReal_mul_im (value : ℂ) :
      ((time : ℂ) * value).im = time * value.im := by
    simp [Complex.mul_im]
  simp_rw [Complex.add_im, ofReal_mul_im]
  ring

/-- On the canonical time axis, the fixed source/action-generated carry
tangency has no hidden scalar, Yukawa, Cartan, or P286 contribution: it is
exactly the transverse primal/independent-adjoint current rate above. -/
theorem
    fixedActionSelectedTimeAxisCarryTangency_eq_transverseDiracCurrentRate
    (direction : LorentzianIndex) (time : ℝ) :
    let point := canonicalCauchySlicePoint time
      (0 : StageNineSpatialPoint)
    let profile := sourceActionGeneratedDiracDualCompleteJointProfiles
      Source Carry point
    (profile.adjointVelocity
        (diracMatrixMatterAction (diracGamma direction)
          (Carry.matter point)) +
      Carry.conjugateMatter point
        (diracMatrixMatterAction (diracGamma direction)
          profile.matterVelocity)).im =
      fixedActionSelectedTimeAxisTransverseDiracCurrentRate direction time := by
  dsimp only
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
  have restartJet := restart_coframeFirstJet_identity
    (canonicalCauchySlicePoint time 0)
  have primalJet := primal_coframeFirstJet_identity
    (canonicalCauchySlicePoint time 0)
  rw [holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
    _ _ primalJet]
  unfold
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeConjugateMatterSpatialTransport
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [coframe_eq_one_of_identity_firstJet _ _ restartJet]
  rw [carry_matter_timeAxis_constant,
    carry_conjugateMatter_timeAxis_constant]
  rw [primal_conjugateMatter_origin_timeAxis]
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterCovariantDerivative holonomicMatterConnectionAction
    holonomicIdentityCoframeMatterConnectionOperator
  rw [congrFun (primal_gravityConnection_eq_restart _) 0,
    congrFun (primal_gaugeConnection_eq_restart _) 0,
    congrFun (primal_scalar_eq_restart _) 0]
  rw [restart_matter_origin_timeAxis]
  rw [restart_gravityConnection_origin_timeAxis_eq_positiveNormalForm]
  rw [restart_scalar_origin_timeAxis_eq_vacuum]
  rw [show scalarCoordinateEquiv.symm
      (sourceGeneratedVacuumCoordinates Source) =
        sourceGeneratedVacuumBase Source by
    simp [sourceGeneratedVacuumCoordinates]]
  rw [
    StageNineDiracDualFormNativeFixedP506JointResidual.fixedP506VacuumDiracDualYukawa_spinTwo_zero]
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.sum_apply,
    map_add, map_sub, map_smul]
  simp_rw [
    StageNineDiracDualFormNativeFixedP506JointResidual.fixedDiracSpinZeroMatterCoordinate_diracDualRightChiralYukawa_zero]
  simp_rw [primal_conjugateMatterDerivativeDual_spatial_timeAxis,
    restart_matterCoordinates_spatialDerivative_timeAxis]
  rw [coframe_eq_one_of_identity_firstJet _ _ restartJet]
  simp_rw [currentCoframeMatterTemporalPrincipalInverse_one]
  rw [Fin.sum_univ_three]
  unfold fixedActionSelectedTimeAxisTransverseDiracCurrentRate
  dsimp only
  rw [Fin.sum_univ_three]
  unfold actionGeneratedCurrentCoframeMatterTemporalDerivative
  simp_rw [currentCoframeMatterTemporalPrincipalInverse_one]
  fin_cases direction <;>
    simp [
      canonicalLorentzianTimeDirection,
      PointwiseDiracSpinConnectionLift.diracSpinConnectionLift,
      StageNineLorentzConnectionVariation.loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      diracExteriorMotherLieAction, internalMatterLinearAction,
      exteriorSpinorMotherLieAction,
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.occupiedExteriorAction_coordinate,
      StageNineMatterActionTimeVelocity.identityCoframeMatterTimePrincipal,
      diracMatrixMatterAction, diracSpinZeroMatterCoordinate,
      hyperchargeDegreeTwoMatterCoordinate,
      diracSpinTwoMatterProbe,
      SU7ExteriorMatterGaugeCovariantJet.p286HyperchargeMatterProbe,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      inverseCoframeDiracGamma_identity,
      Fin.sum_univ_six, Fin.sum_univ_four,
      Fin.sum_univ_three,
      PointwiseDiracSpinConnectionLift.lorentzBivectorFirst,
      PointwiseDiracSpinConnectionLift.lorentzBivectorSecond,
      positiveDiracDualCartanContorsionNormalForm,
      show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
        PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl]
  all_goals
    have gaugeRe (gaugeDirection : LorentzianIndex) :
        ((((Restart (canonicalCauchySlicePoint time 0)).gaugeConnection
              0 gaugeDirection).1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0).re +
            (((Restart (canonicalCauchySlicePoint time 0)).gaugeConnection
              0 gaugeDirection).2.2 : ℂ).re = 0 := by
      simpa only [Complex.add_re] using
        p286_probe_action_eigenvalue_re_zero
          ((Restart (canonicalCauchySlicePoint time 0)).gaugeConnection
            0 gaugeDirection)
    dsimp only [Restart] at gaugeRe ⊢
    ring_nf at ⊢ <;>
      linarith [gaugeRe 0, gaugeRe 1, gaugeRe 2, gaugeRe 3]

/-! ## Source-native settlement of the fixed transverse coefficient -/

local instance unitRateP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  constitutiveRegularityP286ModuleFinite

local instance unitRateP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  constitutiveRegularityP286CoordinateIndexFintype

local instance unitRateP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  constitutiveRegularityP286CoordinateIsTopologicalAddGroup

private abbrev UnitRateFixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private def UnitRateProfile : StageNineHolonomicConfiguration :=
  { UnitRateFixedInput with
    gravityConnection := fun _ =>
      (fixedP506L0CartanRestartActual 0).gravityConnection 0 }

private def UnitRateGaugeModel (gauge : P286GaugeOneForm) :
    StageNineHolonomicConfiguration :=
  { UnitRateProfile with
    gaugeConnection := fun _ direction =>
      p286CoordinateEquiv.symm (gauge direction)
    scalar := fun _ =>
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
    matter := fun _ => diracSpinTwoMatterProbe
    conjugateMatter := fun _ => diracSpinZeroMatterCoordinate }

private theorem unitRateFixedInput_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    UnitRateFixedInput.matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]
  exact fixedP506JointActual_matter_zeroSlice_constant space

private theorem unitRateFixedInput_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    UnitRateFixedInput.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]
  exact fixedP506JointActual_conjugateMatter_zeroSlice_constant space

private theorem unitRateFixedInput_scalar_vacuum (point : BasePoint) :
    UnitRateFixedInput.scalar point =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]

private theorem
    unitRateFixedInput_matterCoordinate_temporalDerivative_zeroSlice_eq_velocityDrift
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (UnitRateFixedInput.matter point))
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
          (actionGeneratedMatterRawTimeVelocity
            positiveP506MatterCurrentFullSynchronizedCauchyState space) -
        matterCoordinateEquiv
          (actionGeneratedMatterRawTimeVelocity
            positiveP506MatterCurrentFullSynchronizedCauchyState 0) := by
  let coefficient : MatterCoordinateCarrier :=
    matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity
          positiveP506MatterCurrentFullSynchronizedCauchyState space) -
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity
          positiveP506MatterCurrentFullSynchronizedCauchyState 0)
  let line : ℝ → MatterCoordinateCarrier := fun time =>
    matterCoordinateEquiv
      (UnitRateFixedInput.matter (canonicalCauchySlicePoint time space))
  have actual := field_timeLine_hasDerivAt
    (fun point => matterCoordinateEquiv (UnitRateFixedInput.matter point))
    space 0
    ((fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
      ).differentiable (by simp) |>.differentiableAt)
  have expected : HasDerivAt line coefficient 0 := by
    rw [show line = fun time =>
        matterCoordinateEquiv diracSpinTwoMatterProbe +
          time • coefficient by
      funext time
      unfold line coefficient UnitRateFixedInput
      rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
        fixedP506JointActionSuccessor_matter]
      exact
        (fixedP506JointActual_matterAdjoint_canonicalVelocityDrift_normalForm
          time space).1]
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const coefficient).const_add
        (matterCoordinateEquiv diracSpinTwoMatterProbe)
  exact actual.unique expected

private theorem
    unitRateFixedInput_conjugateMatterCoordinate_temporalDerivative_zeroSlice_eq_velocityDrift
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates UnitRateFixedInput)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      matterDualCoordinates
          (actionGeneratedConjugateMatterTimeDerivative
            positiveP506MatterCurrentFullSynchronizedCauchyState space) -
        matterDualCoordinates
          (actionGeneratedConjugateMatterTimeDerivative
            positiveP506MatterCurrentFullSynchronizedCauchyState 0) := by
  let coefficient : MatterCoordinateCarrier :=
    matterDualCoordinates
        (actionGeneratedConjugateMatterTimeDerivative
          positiveP506MatterCurrentFullSynchronizedCauchyState space) -
      matterDualCoordinates
        (actionGeneratedConjugateMatterTimeDerivative
          positiveP506MatterCurrentFullSynchronizedCauchyState 0)
  let line : ℝ → MatterCoordinateCarrier := fun time =>
    holonomicConjugateMatterCoordinates UnitRateFixedInput
      (canonicalCauchySlicePoint time space)
  have actual := field_timeLine_hasDerivAt
    (holonomicConjugateMatterCoordinates UnitRateFixedInput) space 0
    ((holonomicConjugateMatterCoordinates_contDiff UnitRateFixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
      ).differentiable (by simp) |>.differentiableAt)
  have expected : HasDerivAt line coefficient 0 := by
    rw [show line = fun time =>
        matterDualCoordinates diracSpinZeroMatterCoordinate +
          time • coefficient by
      funext time
      unfold line coefficient holonomicConjugateMatterCoordinates
        UnitRateFixedInput
      rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
        fixedP506JointActionSuccessor_conjugateMatter]
      have dualEq :
          FixedP506JointActual.conjugateMatter
              (canonicalCauchySlicePoint time space) =
            diracSpinZeroMatterCoordinate +
              time •
                (actionGeneratedConjugateMatterTimeDerivative
                    positiveP506MatterCurrentFullSynchronizedCauchyState
                    space -
                  actionGeneratedConjugateMatterTimeDerivative
                    positiveP506MatterCurrentFullSynchronizedCauchyState
                    0) := by
        apply LinearMap.ext
        intro matter
        simpa only [LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.sub_apply] using
          (fixedP506JointActual_matterAdjoint_canonicalVelocityDrift_normalForm
            time space).2 matter
      rw [dualEq, matterDualCoordinates_add]
      have coordinatesRealSmul
          (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
          matterDualCoordinates (time • dual) =
            time • matterDualCoordinates dual := by
        apply PiLp.ext
        intro index
        simp [matterDualCoordinates]
      rw [coordinatesRealSmul, matterDualCoordinates_sub]]
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const coefficient).const_add
        (matterDualCoordinates diracSpinZeroMatterCoordinate)
  exact actual.unique expected

private theorem unitRateFixedInput_matterCoordinate_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (UnitRateFixedInput.matter point))
        (canonicalCauchySlicePoint 0 space) axis.succ =
      0 := by
  apply spatialDerivative_zero_of_zeroSlice_constant
    (fun point => matterCoordinateEquiv (UnitRateFixedInput.matter point))
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
    (matterCoordinateEquiv diracSpinTwoMatterProbe)
  intro candidate
  exact congrArg matterCoordinateEquiv
    (unitRateFixedInput_matter_zeroSlice candidate)

private theorem
    unitRateFixedInput_conjugateMatterDerivativeDual_spatial_zeroSlice
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    holonomicConjugateMatterDerivativeDual UnitRateFixedInput
        (canonicalCauchySlicePoint 0 space) axis.succ =
      0 := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  rw [spatialDerivative_zero_of_zeroSlice_constant
    (holonomicConjugateMatterCoordinates UnitRateFixedInput)
    (holonomicConjugateMatterCoordinates_contDiff UnitRateFixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth)
    (matterDualCoordinates diracSpinZeroMatterCoordinate)
    (fun candidate => congrArg matterDualCoordinates
      (unitRateFixedInput_conjugateMatter_zeroSlice candidate))]
  exact matterDualOfCoordinates_zero

private theorem unitRateProfile_conjugateMatterDerivativeDual_spatial_zeroSlice
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    holonomicConjugateMatterDerivativeDual UnitRateProfile
        (canonicalCauchySlicePoint 0 space) axis.succ =
      0 := by
  have coordinateEq :
      holonomicConjugateMatterCoordinates UnitRateProfile =
        holonomicConjugateMatterCoordinates UnitRateFixedInput := by
    funext point
    rfl
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  rw [coordinateEq]
  exact
    unitRateFixedInput_conjugateMatterDerivativeDual_spatial_zeroSlice
      space axis

private theorem unitRateGaugeModel_conjugateMatterDerivativeDual_zero
    (gauge : P286GaugeOneForm) (axis : Fin 3) :
    holonomicConjugateMatterDerivativeDual (UnitRateGaugeModel gauge)
        0 axis.succ =
      0 := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates UnitRateGaugeModel
  simp [fieldDirectionalDerivative]

private theorem unitRateProfile_primalVelocity_zeroSlice_eq_gaugeModel
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeMatterRawTimeVelocity UnitRateProfile
        (canonicalCauchySlicePoint 0 space) =
      holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
        (UnitRateGaugeModel
          (holonomicP286GaugeConnectionCoordinate UnitRateFixedInput
            (canonicalCauchySlicePoint 0 space))) 0 := by
  unfold holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
    holonomicDiracDualIdentityCoframeMatterKnownVector
    holonomicMatterCovariantDerivative holonomicMatterConnectionAction
    UnitRateProfile UnitRateGaugeModel
  simp_rw [unitRateFixedInput_matterCoordinate_spatialDerivative_zeroSlice]
  rw [unitRateFixedInput_matter_zeroSlice,
    unitRateFixedInput_scalar_vacuum]
  simp [UnitRateProfile, holonomicP286GaugeConnectionCoordinate,
    p286CoordinateEquiv.symm_apply_apply, fieldDirectionalDerivative]

private theorem unitRateProfile_adjointVelocity_zeroSlice_eq_gaugeModel
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        UnitRateProfile (canonicalCauchySlicePoint 0 space) =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        (UnitRateGaugeModel
          (holonomicP286GaugeConnectionCoordinate UnitRateFixedInput
            (canonicalCauchySlicePoint 0 space))) 0 := by
  apply LinearMap.ext
  intro matter
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp_rw [unitRateProfile_conjugateMatterDerivativeDual_spatial_zeroSlice,
    unitRateGaugeModel_conjugateMatterDerivativeDual_zero]
  unfold UnitRateProfile UnitRateGaugeModel
  rw [unitRateFixedInput_conjugateMatter_zeroSlice,
    unitRateFixedInput_scalar_vacuum]
  simp [UnitRateProfile, holonomicP286GaugeConnectionCoordinate,
    p286CoordinateEquiv.symm_apply_apply]

private def unitRateProfilePrimalGaugeCoordinateLinear :
    P286GaugeOneForm →ₗ[ℝ] MatterCoordinateCarrier where
  toFun gauge := matterCoordinateEquiv
    (-identityCoframeMatterTimePrincipal
        (Complex.I • ∑ direction : Fin 3,
          diracMatrixMatterAction (diracGamma direction.succ)
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed
                (p286CoordinateEquiv.symm (gauge direction.succ)))
              diracSpinTwoMatterProbe)) -
      diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (gauge canonicalLorentzianTimeDirection)))
        diracSpinTwoMatterProbe)
  map_add' first second := by
    rw [← matterCoordinateEquiv.map_add]
    congr 1
    unfold identityCoframeMatterTimePrincipal
    simp only [Pi.add_apply, p286CoordinateEquiv.symm.map_add,
      p286LieBlockEmbed_add, diracExteriorMotherLieAction_add,
      LinearMap.add_apply, map_add, Finset.sum_add_distrib, smul_add]
    module
  map_smul' parameter gauge := by
    rw [← matterCoordinateEquiv_real_smul]
    congr 1
    unfold identityCoframeMatterTimePrincipal
    simp only [Pi.smul_apply, p286CoordinateEquiv.symm.map_smul,
      p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul,
      LinearMap.smul_apply, map_smul, RingHom.id_apply]
    have coe_smul_eq_real_smul (value : DiracExteriorMatterCarrier) :
        (parameter : ℂ) • value = parameter • value := by
      rfl
    rw [← coe_smul_eq_real_smul]
    have complex_smul_comm (value : DiracExteriorMatterCarrier) :
        Complex.I • (parameter : ℂ) • value =
          (parameter : ℂ) • Complex.I • value := by
      exact smul_comm Complex.I (parameter : ℂ) value
    rw [← Finset.smul_sum, map_smul]
    simp_rw [complex_smul_comm]
    module

private def unitRateProfilePrimalGaugeCoordinateCLM :
    P286GaugeOneForm →L[ℝ] MatterCoordinateCarrier :=
  unitRateProfilePrimalGaugeCoordinateLinear.toContinuousLinearMap

private def unitRateProfileAdjointGaugeCoordinateLinear :
    P286GaugeOneForm →ₗ[ℝ] MatterCoordinateCarrier where
  toFun gauge := matterDualCoordinates
    ((diracSpinZeroMatterCoordinate.comp
        (Complex.I • ∑ direction : LorentzianIndex,
          (diracMatrixMatterAction (diracGamma direction)).comp
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed
                (p286CoordinateEquiv.symm (gauge direction)))))).comp
      (identityCoframeMatterPrincipal
        canonicalLorentzianTimeDirection))
  map_add' first second := by
    rw [← matterDualCoordinates_add]
    apply congrArg matterDualCoordinates
    apply LinearMap.ext
    intro matter
    simp only [Pi.add_apply,
      p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
      diracExteriorMotherLieAction_add, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      map_add, Finset.sum_add_distrib, smul_add]
  map_smul' parameter gauge := by
    simp only [RingHom.id_apply]
    have coordinatesRealSmul
        (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
        matterDualCoordinates (parameter • dual) =
          parameter • matterDualCoordinates dual := by
      apply PiLp.ext
      intro index
      simp [matterDualCoordinates]
    rw [← coordinatesRealSmul]
    apply congrArg matterDualCoordinates
    apply LinearMap.ext
    intro matter
    simp only [Pi.smul_apply,
      p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
      diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.sum_apply, map_smul, RingHom.id_apply]
    rw [← Finset.smul_sum, map_smul]
    exact smul_comm Complex.I (parameter : ℂ) _

private def unitRateProfileAdjointGaugeCoordinateCLM :
    P286GaugeOneForm →L[ℝ] MatterCoordinateCarrier :=
  unitRateProfileAdjointGaugeCoordinateLinear.toContinuousLinearMap

@[simp] private theorem unitRateProfileAdjointGaugeCoordinateLinear_apply
    (gauge : P286GaugeOneForm) :
    unitRateProfileAdjointGaugeCoordinateLinear gauge =
      matterDualCoordinates
        ((diracSpinZeroMatterCoordinate.comp
            (Complex.I • ∑ direction : LorentzianIndex,
              (diracMatrixMatterAction (diracGamma direction)).comp
                (diracExteriorMotherLieAction
                  (p286LieBlockEmbed
                    (p286CoordinateEquiv.symm (gauge direction)))))).comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection)) :=
  rfl

@[simp] private theorem unitRateProfileAdjointGaugeCoordinateCLM_apply
    (gauge : P286GaugeOneForm) :
    unitRateProfileAdjointGaugeCoordinateCLM gauge =
      unitRateProfileAdjointGaugeCoordinateLinear gauge :=
  rfl

@[simp] private theorem unitRateProfilePrimalGaugeCoordinateLinear_apply
    (gauge : P286GaugeOneForm) :
    unitRateProfilePrimalGaugeCoordinateLinear gauge =
      matterCoordinateEquiv
        (-identityCoframeMatterTimePrincipal
            (Complex.I • ∑ direction : Fin 3,
              diracMatrixMatterAction (diracGamma direction.succ)
                (diracExteriorMotherLieAction
                  (p286LieBlockEmbed
                    (p286CoordinateEquiv.symm (gauge direction.succ)))
                  diracSpinTwoMatterProbe)) -
          diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (gauge canonicalLorentzianTimeDirection)))
            diracSpinTwoMatterProbe) :=
  rfl

@[simp] private theorem unitRateProfilePrimalGaugeCoordinateCLM_apply
    (gauge : P286GaugeOneForm) :
    unitRateProfilePrimalGaugeCoordinateCLM gauge =
      unitRateProfilePrimalGaugeCoordinateLinear gauge :=
  rfl

private theorem unitRateProfile_primalVelocity_zeroSlice_coordinate_normalForm
    (space : StageNineSpatialPoint) :
    matterCoordinateEquiv
        (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity UnitRateProfile
          (canonicalCauchySlicePoint 0 space)) =
      matterCoordinateEquiv
          (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
            (UnitRateGaugeModel 0) 0) +
        unitRateProfilePrimalGaugeCoordinateCLM
          (holonomicP286GaugeConnectionCoordinate UnitRateFixedInput
            (canonicalCauchySlicePoint 0 space)) := by
  rw [unitRateProfile_primalVelocity_zeroSlice_eq_gaugeModel,
    unitRateProfilePrimalGaugeCoordinateCLM_apply,
    unitRateProfilePrimalGaugeCoordinateLinear_apply]
  unfold holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
    holonomicDiracDualIdentityCoframeMatterKnownVector
    holonomicMatterCovariantDerivative holonomicMatterConnectionAction
    UnitRateGaugeModel UnitRateProfile
  simp only [fieldDirectionalDerivative, fderiv_const, zero_apply,
    matterCoordinateEquiv.map_zero, matterCoordinateEquiv.symm_apply_apply,
    holonomicP286GaugeConnectionCoordinate,
    p286CoordinateEquiv.symm_apply_apply, Pi.zero_apply,
    p286CoordinateEquiv.symm.map_zero, p286LieBlockEmbed_zero,
    diracExteriorMotherLieAction_zero_matrix, LinearMap.zero_apply]
  rw [← matterCoordinateEquiv.map_add]
  congr 1
  unfold identityCoframeMatterTimePrincipal
  simp only [LinearMap.add_apply, map_add, map_zero,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_add, smul_zero,
    add_zero]
  abel

private theorem unitRateProfile_adjointVelocity_zeroSlice_coordinate_normalForm
    (space : StageNineSpatialPoint) :
    matterDualCoordinates
        (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          UnitRateProfile (canonicalCauchySlicePoint 0 space)) =
      matterDualCoordinates
          (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
            (UnitRateGaugeModel 0) 0) +
        unitRateProfileAdjointGaugeCoordinateCLM
          (holonomicP286GaugeConnectionCoordinate UnitRateFixedInput
            (canonicalCauchySlicePoint 0 space)) := by
  rw [unitRateProfile_adjointVelocity_zeroSlice_eq_gaugeModel,
    unitRateProfileAdjointGaugeCoordinateCLM_apply,
    unitRateProfileAdjointGaugeCoordinateLinear_apply,
    ← matterDualCoordinates_add]
  apply congrArg matterDualCoordinates
  apply LinearMap.ext
  intro matter
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp_rw [unitRateGaugeModel_conjugateMatterDerivativeDual_zero]
  unfold UnitRateGaugeModel
  simp only [Pi.zero_apply, p286CoordinateEquiv.symm.map_zero,
    p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix,
    LinearMap.zero_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    map_zero, map_add, Finset.sum_add_distrib, Finset.sum_const_zero,
    smul_add, smul_zero, add_zero]
  abel

private theorem unitRateProfile_primalVelocity_zeroSlice_fderiv_axis_zero
    (axis : Fin 3) :
    fderiv ℝ
        (fun space : StageNineSpatialPoint =>
          matterCoordinateEquiv
            (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
              UnitRateProfile (canonicalCauchySlicePoint 0 space)))
        0 (canonicalSpatialCoordinateDirection axis) =
      0 := by
  let inner : StageNineSpatialPoint → P286GaugeOneForm :=
    holonomicP286GaugeConnectionCoordinate UnitRateFixedInput ∘
      canonicalCauchySlicePoint 0
  have innerDifferentiable : DifferentiableAt ℝ inner 0 :=
    ((holonomicP286GaugeConnectionCoordinate_contDiff UnitRateFixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth).comp
        StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity.canonicalZeroSlice_contDiff
      ).differentiable (by simp)
      |>.differentiableAt
  have composed := unitRateProfilePrimalGaugeCoordinateCLM.hasFDerivAt.comp 0
    innerDifferentiable.hasFDerivAt
  have total :=
    (hasFDerivAt_const (x := (0 : StageNineSpatialPoint))
      (matterCoordinateEquiv
        (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
          (UnitRateGaugeModel 0) 0))).add composed
  have functionEquality :
      (fun space : StageNineSpatialPoint =>
        matterCoordinateEquiv
          (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
            UnitRateProfile (canonicalCauchySlicePoint 0 space))) =
        (fun _ : StageNineSpatialPoint =>
          matterCoordinateEquiv
            (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
              (UnitRateGaugeModel 0) 0)) +
          unitRateProfilePrimalGaugeCoordinateCLM ∘ inner := by
    funext space
    exact
      unitRateProfile_primalVelocity_zeroSlice_coordinate_normalForm space
  rw [functionEquality, total.fderiv]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, zero_add,
    ContinuousLinearMap.comp_apply]
  change
    unitRateProfilePrimalGaugeCoordinateCLM
        ((fderiv ℝ inner 0)
          (canonicalSpatialCoordinateDirection axis)) =
      0
  rw [show
    (fderiv ℝ inner 0) (canonicalSpatialCoordinateDirection axis) = 0 by
      exact
        fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_zeroSlice_fderiv_axis_zero
          axis]
  simp [identityCoframeMatterTimePrincipal]

private theorem unitRateProfile_adjointVelocity_zeroSlice_fderiv_axis_zero
    (axis : Fin 3) :
    fderiv ℝ
        (fun space : StageNineSpatialPoint =>
          matterDualCoordinates
            (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
              UnitRateProfile (canonicalCauchySlicePoint 0 space)))
        0 (canonicalSpatialCoordinateDirection axis) =
      0 := by
  let inner : StageNineSpatialPoint → P286GaugeOneForm :=
    holonomicP286GaugeConnectionCoordinate UnitRateFixedInput ∘
      canonicalCauchySlicePoint 0
  have innerDifferentiable : DifferentiableAt ℝ inner 0 :=
    ((holonomicP286GaugeConnectionCoordinate_contDiff UnitRateFixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth).comp
        StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity.canonicalZeroSlice_contDiff
      ).differentiable (by simp)
      |>.differentiableAt
  have composed := unitRateProfileAdjointGaugeCoordinateCLM.hasFDerivAt.comp 0
    innerDifferentiable.hasFDerivAt
  have total :=
    (hasFDerivAt_const (x := (0 : StageNineSpatialPoint))
      (matterDualCoordinates
        (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          (UnitRateGaugeModel 0) 0))).add composed
  have functionEquality :
      (fun space : StageNineSpatialPoint =>
        matterDualCoordinates
          (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
            UnitRateProfile (canonicalCauchySlicePoint 0 space))) =
        (fun _ : StageNineSpatialPoint =>
          matterDualCoordinates
            (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
              (UnitRateGaugeModel 0) 0)) +
          unitRateProfileAdjointGaugeCoordinateCLM ∘ inner := by
    funext space
    exact
      unitRateProfile_adjointVelocity_zeroSlice_coordinate_normalForm space
  rw [functionEquality, total.fderiv]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, zero_add,
    ContinuousLinearMap.comp_apply]
  change
    unitRateProfileAdjointGaugeCoordinateCLM
        ((fderiv ℝ inner 0)
          (canonicalSpatialCoordinateDirection axis)) =
      0
  rw [show
    (fderiv ℝ inner 0) (canonicalSpatialCoordinateDirection axis) = 0 by
      exact
        fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_zeroSlice_fderiv_axis_zero
          axis]
  apply PiLp.ext
  intro index
  simp [matterDualCoordinates, diracExteriorMotherLieAction_zero_matrix]

private theorem unitRateMatterResponseWrite_profile
    (space : StageNineSpatialPoint) :
    diracDualCurrentCoframeMatterTimeResponseWrite
        (fixedP506L0CartanRestartActual space) =
      holonomicDiracDualIdentityCoframeMatterRawTimeVelocity UnitRateProfile
          (canonicalCauchySlicePoint 0 space) -
        matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv
              (UnitRateFixedInput.matter point))
            (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection) := by
  simpa [UnitRateProfile, UnitRateFixedInput] using
    fixedP506L0CompleteJointMatterResponseWrite_sourceFields space

private theorem unitRateAdjointResponseWrite_profile
    (space : StageNineSpatialPoint) :
    liveCoframeConjugateMatterTimeResponseWrite
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space)) =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          UnitRateProfile (canonicalCauchySlicePoint 0 space) -
        holonomicConjugateMatterDerivativeDual UnitRateProfile
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  simpa [UnitRateProfile, UnitRateFixedInput] using
    fixedP506L0CompleteJointAdjointResponseWrite_sourceFields space

private theorem unitRateProfile_conjugateMatterDerivativeDual_eq_fixedInput
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual UnitRateProfile point direction =
      holonomicConjugateMatterDerivativeDual UnitRateFixedInput
        point direction := by
  have coordinateEq :
      holonomicConjugateMatterCoordinates UnitRateProfile =
        holonomicConjugateMatterCoordinates UnitRateFixedInput := by
    funext candidate
    rfl
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  rw [coordinateEq]

private theorem timeAxisPrimalSpatialRateCoordinates_eq_unitRateProfileVelocity
    (space : StageNineSpatialPoint) :
    timeAxisPrimalSpatialRateCoordinates space =
      matterCoordinateEquiv
        (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
          UnitRateProfile (canonicalCauchySlicePoint 0 space)) := by
  unfold timeAxisPrimalSpatialRateCoordinates
  rw [unitRateMatterResponseWrite_profile]
  rw [map_sub, matterCoordinateEquiv.apply_symm_apply]
  rw [unitRateFixedInput_matterCoordinate_temporalDerivative_zeroSlice_eq_velocityDrift]
  abel

private theorem timeAxisAdjointSpatialRateCoordinates_eq_unitRateProfileVelocity
    (space : StageNineSpatialPoint) :
    timeAxisAdjointSpatialRateCoordinates space =
      matterDualCoordinates
        (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          UnitRateProfile (canonicalCauchySlicePoint 0 space)) := by
  unfold timeAxisAdjointSpatialRateCoordinates
  rw [unitRateAdjointResponseWrite_profile]
  rw [matterDualCoordinates_sub]
  rw [unitRateProfile_conjugateMatterDerivativeDual_eq_fixedInput]
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  rw [matterDualCoordinates_matterDualOfCoordinates]
  rw [unitRateFixedInput_conjugateMatterCoordinate_temporalDerivative_zeroSlice_eq_velocityDrift]
  abel

private theorem timeAxisPrimalSpatialRateCoordinates_fderiv_axis_zero
    (axis : Fin 3) :
    fderiv ℝ timeAxisPrimalSpatialRateCoordinates 0
        (canonicalSpatialCoordinateDirection axis) =
      0 := by
  rw [show timeAxisPrimalSpatialRateCoordinates = fun space =>
      matterCoordinateEquiv
        (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
          UnitRateProfile (canonicalCauchySlicePoint 0 space)) by
    funext space
    exact
      timeAxisPrimalSpatialRateCoordinates_eq_unitRateProfileVelocity space]
  exact unitRateProfile_primalVelocity_zeroSlice_fderiv_axis_zero axis

private theorem timeAxisAdjointSpatialRateCoordinates_fderiv_axis_zero
    (axis : Fin 3) :
    fderiv ℝ timeAxisAdjointSpatialRateCoordinates 0
        (canonicalSpatialCoordinateDirection axis) =
      0 := by
  rw [show timeAxisAdjointSpatialRateCoordinates = fun space =>
      matterDualCoordinates
        (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          UnitRateProfile (canonicalCauchySlicePoint 0 space)) by
    funext space
    exact
      timeAxisAdjointSpatialRateCoordinates_eq_unitRateProfileVelocity space]
  exact unitRateProfile_adjointVelocity_zeroSlice_fderiv_axis_zero axis

/-- The fixed source/action writer itself settles the canonical time-axis
transverse coefficient.  No target current equation or settlement witness is
accepted from the caller. -/
theorem fixedActionSelectedTimeAxisTransverseDiracCurrentRate_unit_zero
    (direction : LorentzianIndex) :
    fixedActionSelectedTimeAxisTransverseDiracCurrentRate direction 1 = 0 := by
  unfold fixedActionSelectedTimeAxisTransverseDiracCurrentRate
  dsimp only
  simp_rw [carry_matter_spatialDerivative_timeAxis_affine,
    carry_adjoint_spatialDerivative_timeAxis_affine]
  simp_rw [one_smul,
    timeAxisPrimalSpatialRateCoordinates_fderiv_axis_zero,
    timeAxisAdjointSpatialRateCoordinates_fderiv_axis_zero]
  simp [actionGeneratedCurrentCoframeMatterTemporalDerivative]

/-- Source-native all-time settlement of the fixed transverse rate. -/
theorem fixedActionSelectedTimeAxisTransverseDiracCurrentRate_zero
    (direction : LorentzianIndex) (time : ℝ) :
    fixedActionSelectedTimeAxisTransverseDiracCurrentRate direction time = 0 := by
  rw [fixedActionSelectedTimeAxisTransverseDiracCurrentRate_eq_time_mul_unit,
    fixedActionSelectedTimeAxisTransverseDiracCurrentRate_unit_zero, mul_zero]

private theorem carry_matter_spatialDerivative_timeAxis_zero
    (time : ℝ) (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point))
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        direction.succ = 0 := by
  rw [carry_matter_spatialDerivative_timeAxis_affine,
    timeAxisPrimalSpatialRateCoordinates_fderiv_axis_zero, smul_zero]

private theorem carry_adjoint_spatialDerivative_timeAxis_zero
    (time : ℝ) (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry)
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        direction.succ = 0 := by
  rw [carry_adjoint_spatialDerivative_timeAxis_affine,
    timeAxisAdjointSpatialRateCoordinates_fderiv_axis_zero, smul_zero]

private theorem restart_gaugeConnection_origin_timeAxis_coordinate
    (time : ℝ) (direction : LorentzianIndex) :
    p286CoordinateEquiv
        ((Restart (canonicalCauchySlicePoint time 0)).gaugeConnection
          0 direction) =
      (-c3h181FullConnectionCoefficient
          (-(canonicalCauchySlicePoint time 0)) direction) •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  unfold Restart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    fullyRecenterHolonomicConfiguration_gaugeConnection_origin]
  exact
    actionSelectedCarry_gaugeConnectionCoordinate_timeAxis_normalForm
      time direction

private theorem canonicalTimeAxis_origin :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem restart_coframe_origin_timeAxis_one (time : ℝ) :
    (Restart (canonicalCauchySlicePoint time 0)).coframe 0 = 1 := by
  exact coframe_eq_one_of_identity_firstJet _ _
    (restart_coframeFirstJet_identity (canonicalCauchySlicePoint time 0))

private theorem restart_coframe_origin_one :
    (Restart 0).coframe 0 = 1 := by
  simpa only [canonicalTimeAxis_origin] using
    restart_coframe_origin_timeAxis_one 0

private theorem restart_matter_origin :
    (Restart 0).matter 0 = diracSpinTwoMatterProbe := by
  simpa only [canonicalTimeAxis_origin] using
    restart_matter_origin_timeAxis 0

private theorem restart_scalar_origin_eq_vacuum :
    (Restart 0).scalar 0 = sourceGeneratedVacuumCoordinates Source := by
  simpa only [canonicalTimeAxis_origin] using
    restart_scalar_origin_timeAxis_eq_vacuum 0

private theorem restart_gravityConnection_origin_eq_positiveNormalForm :
    (Restart 0).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveDiracDualCartanContorsionNormalForm := by
  simpa only [canonicalTimeAxis_origin] using
    restart_gravityConnection_origin_timeAxis_eq_positiveNormalForm 0

private theorem restart_matterCoordinates_spatialDerivative_origin_zero
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv ((Restart 0).matter localPoint))
        0 direction.succ = 0 := by
  simpa only [canonicalTimeAxis_origin] using
    (restart_matterCoordinates_spatialDerivative_timeAxis 0 direction).trans
      (carry_matter_spatialDerivative_timeAxis_zero 0 direction)

private theorem restart_gaugeConnection_origin_zero
    (direction : LorentzianIndex) :
    (Restart 0).gaugeConnection 0 direction = 0 := by
  have normal :=
    restart_gaugeConnection_origin_timeAxis_coordinate 0 direction
  rw [canonicalTimeAxis_origin] at normal
  apply p286CoordinateEquiv.injective
  rw [normal]
  fin_cases direction <;>
    simp [c3h181FullConnectionCoefficient,
      canonicalLorentzianTimeDirection]

private theorem restart_matterCovariantDerivative_timeAxis_eq_origin_add_gauge
    (time : ℝ) (axis : Fin 3) :
    holonomicMatterCovariantDerivative
        (Restart (canonicalCauchySlicePoint time 0)) 0 axis.succ =
      holonomicMatterCovariantDerivative (Restart 0) 0 axis.succ +
        diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              ((-c3h181FullConnectionCoefficient
                  (-(canonicalCauchySlicePoint time 0)) axis.succ) •
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
          diracSpinTwoMatterProbe := by
  unfold holonomicMatterCovariantDerivative
  rw [restart_matter_origin_timeAxis, restart_matter_origin,
    restart_gravityConnection_origin_timeAxis_eq_positiveNormalForm,
    restart_gravityConnection_origin_eq_positiveNormalForm,
    restart_matterCoordinates_spatialDerivative_timeAxis,
    carry_matter_spatialDerivative_timeAxis_zero,
    restart_matterCoordinates_spatialDerivative_origin_zero,
    restart_gaugeConnection_origin_zero]
  have restartGauge :
      (Restart (canonicalCauchySlicePoint time 0)).gaugeConnection 0 axis.succ =
        p286CoordinateEquiv.symm
          ((-c3h181FullConnectionCoefficient
              (-(canonicalCauchySlicePoint time 0)) axis.succ) •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) := by
    apply p286CoordinateEquiv.injective
    rw [restart_gaugeConnection_origin_timeAxis_coordinate,
      p286CoordinateEquiv.apply_symm_apply]
  rw [restartGauge]
  simp [diracExteriorMotherLieAction_zero_matrix]

private theorem restart_knownVector_timeAxis_eq_origin_add_gauge
    (time : ℝ) :
    let point := canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)
    let gaugeSpatialKnown : DiracExteriorMatterCarrier :=
      ∑ axis : Fin 3,
        identityCoframeMatterPrincipal axis.succ
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                ((-c3h181FullConnectionCoefficient (-point) axis.succ) •
                  positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
            diracSpinTwoMatterProbe)
    holonomicDiracDualCurrentCoframeMatterKnownVector (Restart point) 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector (Restart 0) 0 +
        gaugeSpatialKnown := by
  dsimp only
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [restart_coframe_origin_timeAxis_one, restart_coframe_origin_one,
    restart_scalar_origin_timeAxis_eq_vacuum, restart_scalar_origin_eq_vacuum,
    restart_matter_origin_timeAxis, restart_matter_origin]
  simp_rw [restart_matterCovariantDerivative_timeAxis_eq_origin_add_gauge]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp only [identityCoframeMatterPrincipal_apply, map_add,
    Finset.sum_add_distrib, smul_add]
  simp_rw [Finset.smul_sum]
  abel

private theorem restart_connectionAction_timeAxis_eq_origin (time : ℝ) :
    holonomicMatterConnectionAction
        (Restart (canonicalCauchySlicePoint time 0)) 0
        canonicalLorentzianTimeDirection =
      holonomicMatterConnectionAction (Restart 0) 0
        canonicalLorentzianTimeDirection := by
  unfold holonomicMatterConnectionAction
  rw [restart_matter_origin_timeAxis, restart_matter_origin,
    restart_gravityConnection_origin_timeAxis_eq_positiveNormalForm,
    restart_gravityConnection_origin_eq_positiveNormalForm,
    restart_gaugeConnection_origin_zero]
  have timeGaugeZero :
      (Restart (canonicalCauchySlicePoint time 0)).gaugeConnection 0
          canonicalLorentzianTimeDirection = 0 := by
    apply p286CoordinateEquiv.injective
    simpa [c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three] using
      restart_gaugeConnection_origin_timeAxis_coordinate time
        canonicalLorentzianTimeDirection
  rw [timeGaugeZero]

/-- On the canonical time axis the fixed matter profile has no residual
spatial, scalar, or Cartan contribution.  Its complete velocity is the
source-generated P286 connection polynomial acting on the fixed probe. -/
theorem fixedActionSelectedTimeAxisMatterVelocity_gaugePolynomial_normalForm
    (time : ℝ) :
    let point := canonicalCauchySlicePoint time
      (0 : StageNineSpatialPoint)
    let charge :=
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
    let gaugeSpatialKnown : DiracExteriorMatterCarrier :=
      ∑ axis : Fin 3,
        identityCoframeMatterPrincipal axis.succ
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                ((-c3h181FullConnectionCoefficient (-point) axis.succ) •
                  charge)))
            diracSpinTwoMatterProbe)
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry point
      ).matterVelocity =
      actionGeneratedCurrentCoframeMatterTemporalDerivative 1
        gaugeSpatialKnown := by
  dsimp only
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
  change
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (Restart (canonicalCauchySlicePoint time 0)) 0 = _
  calc
    _ = actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          (Restart 0) 0 +
        actionGeneratedCurrentCoframeMatterTemporalDerivative 1
          (∑ axis : Fin 3,
            identityCoframeMatterPrincipal axis.succ
              (diracExteriorMotherLieAction
                (p286LieBlockEmbed
                  (p286CoordinateEquiv.symm
                    ((-c3h181FullConnectionCoefficient
                        (-(canonicalCauchySlicePoint time 0)) axis.succ) •
                      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
                diracSpinTwoMatterProbe)) := by
      unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
      rw [restart_coframe_origin_timeAxis_one, restart_coframe_origin_one,
        restart_knownVector_timeAxis_eq_origin_add_gauge,
        restart_connectionAction_timeAxis_eq_origin]
      unfold actionGeneratedCurrentCoframeMatterTemporalDerivative
      rw [map_add, neg_add_rev]
      abel
    _ = _ := by
      rw [← sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity
        Source Carry 0,
        fixedP506L0ActionSelectedCoupledTemporalProfile_matterVelocity_zero]
      simp

/-- The fixed action-selected matter velocity on the canonical time axis is
the exact polynomial emitted by its source-generated P506 Gauss charge. -/
theorem fixedActionSelectedTimeAxisMatterVelocity_normalForm
    (time : ℝ) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
    ).matterVelocity =
      fun spinIndex =>
        if spinIndex = 3 then
          (Complex.I * ((5 / 9 : ℝ) *
            c3h181StrongCouplingSquared * time)) •
              p286HyperchargeMatterProbe
        else if spinIndex = 2 then
          (Complex.I * ((5 / 6 : ℝ) *
            c3h181StrongCouplingSquared * time ^ 2)) •
              p286HyperchargeMatterProbe
        else 0 := by
  rw [fixedActionSelectedTimeAxisMatterVelocity_gaugePolynomial_normalForm]
  simp_rw [p286CoordinateEquiv.symm.map_smul,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul]
  simp only [LinearMap.smul_apply]
  rw [
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.currentGaussCharge_spinTwo_action_normalForm]
  funext spinIndex
  fin_cases spinIndex <;>
    simp [actionGeneratedCurrentCoframeMatterTemporalDerivative,
      currentCoframeMatterTemporalPrincipalInverse_one,
      identityCoframeMatterPrincipal,
      StageNineMatterActionTimeVelocity.identityCoframeMatterTimePrincipal,
      c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three,
      diracMatrixMatterAction, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, diracSpinTwoMatterProbe,
      p286HyperchargeMatterProbe, Pi.smul_apply, smul_smul,
      Fin.sum_univ_four, pow_succ]
  all_goals
    rw [← neg_smul]
    congr 1 <;>
      norm_num [pow_succ, Complex.I_mul_I] <;>
      ring
  all_goals
    rw [show Complex.I ^ 3 = -Complex.I by norm_num]
    ring

private def timeAxisGaugeAdjointAlgebraicOperator
    (time : ℝ) : Module.End ℂ DiracExteriorMatterCarrier :=
  let point := canonicalCauchySlicePoint time
    (0 : StageNineSpatialPoint)
  ∑ direction : LorentzianIndex,
    (identityCoframeMatterPrincipal direction).comp
      (diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            ((-c3h181FullConnectionCoefficient (-point) direction) •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))))

private theorem restart_gaugeConnection_origin_timeAxis
    (time : ℝ) (direction : LorentzianIndex) :
    (Restart (canonicalCauchySlicePoint time 0)).gaugeConnection 0 direction =
      p286CoordinateEquiv.symm
        ((-c3h181FullConnectionCoefficient
            (-(canonicalCauchySlicePoint time 0)) direction) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) := by
  apply p286CoordinateEquiv.injective
  rw [restart_gaugeConnection_origin_timeAxis_coordinate,
    p286CoordinateEquiv.apply_symm_apply]

private theorem primal_identityMatterConnectionOperator_timeAxis_eq_origin_add_gauge
    (time : ℝ) (direction : LorentzianIndex) :
    holonomicIdentityCoframeMatterConnectionOperator
        (Primal (canonicalCauchySlicePoint time 0)) 0 direction =
      holonomicIdentityCoframeMatterConnectionOperator (Primal 0) 0 direction +
        diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              ((-c3h181FullConnectionCoefficient
                  (-(canonicalCauchySlicePoint time 0)) direction) •
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))) := by
  unfold holonomicIdentityCoframeMatterConnectionOperator
  rw [congrFun (primal_gravityConnection_eq_restart _) 0,
    congrFun (primal_gravityConnection_eq_restart 0) 0,
    congrFun (primal_gaugeConnection_eq_restart _) 0,
    congrFun (primal_gaugeConnection_eq_restart 0) 0,
    restart_gravityConnection_origin_timeAxis_eq_positiveNormalForm,
    restart_gravityConnection_origin_eq_positiveNormalForm,
    restart_gaugeConnection_origin_timeAxis,
    restart_gaugeConnection_origin_zero]
  rw [p286LieBlockEmbed_zero]
  apply LinearMap.ext
  intro matter
  simp only [LinearMap.add_apply,
    diracExteriorMotherLieAction_zero_matrix, add_zero]

private theorem primal_rightChiralAlgebraicOperator_timeAxis_eq_origin_add_gauge
    (time : ℝ) :
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
        (Primal (canonicalCauchySlicePoint time 0)) 0 =
      holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
          (Primal 0) 0 +
        timeAxisGaugeAdjointAlgebraicOperator time := by
  unfold
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
    timeAxisGaugeAdjointAlgebraicOperator
  rw [congrFun (primal_scalar_eq_restart _) 0,
    congrFun (primal_scalar_eq_restart 0) 0,
    restart_scalar_origin_timeAxis_eq_vacuum,
    restart_scalar_origin_eq_vacuum]
  simp_rw [primal_identityMatterConnectionOperator_timeAxis_eq_origin_add_gauge]
  simp_rw [LinearMap.comp_add]
  rw [Finset.sum_add_distrib]
  abel

private theorem primal_adjointSpatialTransport_timeAxis_zero
    (time : ℝ) :
    holonomicIdentityCoframeConjugateMatterSpatialTransport
        (Primal (canonicalCauchySlicePoint time 0)) 0 = 0 := by
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp_rw [primal_conjugateMatterDerivativeDual_spatial_timeAxis,
    carry_adjoint_spatialDerivative_timeAxis_zero]
  simp

private theorem primal_rightChiralKnownDual_timeAxis_eq_origin_add_gauge
    (time : ℝ) :
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
        (Primal (canonicalCauchySlicePoint time 0)) 0 =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
          (Primal 0) 0 +
        diracSpinZeroMatterCoordinate.comp
          (timeAxisGaugeAdjointAlgebraicOperator time) := by
  unfold holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
  rw [primal_conjugateMatter_origin_timeAxis]
  have originConjugate :
      (Primal 0).conjugateMatter 0 = diracSpinZeroMatterCoordinate := by
    simpa only [canonicalTimeAxis_origin] using
      primal_conjugateMatter_origin_timeAxis 0
  rw [originConjugate,
    primal_rightChiralAlgebraicOperator_timeAxis_eq_origin_add_gauge,
    primal_adjointSpatialTransport_timeAxis_zero]
  have originTransport :
      holonomicIdentityCoframeConjugateMatterSpatialTransport
          (Primal 0) 0 = 0 := by
    simpa only [canonicalTimeAxis_origin] using
      primal_adjointSpatialTransport_timeAxis_zero 0
  rw [originTransport]
  apply LinearMap.ext
  intro matter
  simp [LinearMap.comp_apply]

/-- On the canonical time axis the independent adjoint profile is exactly the
dual P506 connection polynomial emitted by the same fixed source charge. -/
private theorem fixedActionSelectedTimeAxisAdjointVelocity_gaugePolynomial_normalForm
    (time : ℝ) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
    ).adjointVelocity =
      (diracSpinZeroMatterCoordinate.comp
        (timeAxisGaugeAdjointAlgebraicOperator time)).comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
  change
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (Primal (canonicalCauchySlicePoint time 0)) 0 = _
  have primalJet := primal_coframeFirstJet_identity
    (canonicalCauchySlicePoint time 0)
  rw [
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
      _ _ primalJet]
  unfold
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
  rw [primal_rightChiralKnownDual_timeAxis_eq_origin_add_gauge]
  have originJet := primal_coframeFirstJet_identity 0
  have originVelocity :
      (holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
          (Primal 0) 0).comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) = 0 := by
    change
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          (Primal 0) 0 = 0
    rw [←
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ originJet]
    rw [← sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity
      Source Carry 0,
      fixedP506L0ActionSelectedCoupledTemporalProfile_adjointVelocity_zero]
  apply LinearMap.ext
  intro matter
  have originAt := congrArg (fun dual => dual matter) originVelocity
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply] at originAt ⊢
  rw [originAt, zero_add]

/-- The independent adjoint profile is the source-generated two-coordinate
dual polynomial.  This statement applies to every matter carrier, so its
later primitive is an actual physical dual rather than a probe table. -/
theorem fixedActionSelectedTimeAxisAdjointVelocity_apply_normalForm
    (time : ℝ) (matter : DiracExteriorMatterCarrier) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
    ).adjointVelocity matter =
      -(Complex.I * ((5 / 6 : ℝ) *
          c3h181StrongCouplingSquared * time ^ 2)) *
        hyperchargeDegreeTwoMatterCoordinate (matter 0) -
      (Complex.I * ((5 / 9 : ℝ) *
          c3h181StrongCouplingSquared * time)) *
        hyperchargeDegreeTwoMatterCoordinate (matter 1) := by
  rw [fixedActionSelectedTimeAxisAdjointVelocity_gaugePolynomial_normalForm]
  unfold timeAxisGaugeAdjointAlgebraicOperator
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  simp_rw [StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.currentGaussCharge_realSmul_diracCoordinate_principal_action_normalForm]
  simp [identityCoframeMatterPrincipal,
    StageNineMatterActionTimeVelocity.identityCoframeMatterTimePrincipal,
    c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
    canonicalLorentzianTimeDirection, Fin.sum_univ_four,
    diracMatrixMatterAction, diracGamma, diracGammaZero,
    diracGammaOne, diracGammaTwo, diracGammaThree,
    diracSpinZeroMatterCoordinate, Fin.sum_univ_three,
    smul_smul, pow_succ]
  ring_nf

/-- Exact fixed-source adjoint response on the four Dirac-current probes. -/
theorem fixedActionSelectedTimeAxisAdjointVelocity_diracProbe_normalForm
    (time : ℝ) (direction : LorentzianIndex) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
    ).adjointVelocity
        (diracMatrixMatterAction (diracGamma direction)
          diracSpinTwoMatterProbe) =
      ![
        -(Complex.I * ((5 / 6 : ℝ) *
          c3h181StrongCouplingSquared * time ^ 2)),
        -(Complex.I * ((5 / 9 : ℝ) *
          c3h181StrongCouplingSquared * time)),
        ((5 / 9 : ℝ) * c3h181StrongCouplingSquared * time : ℂ),
        -(Complex.I * ((5 / 6 : ℝ) *
          c3h181StrongCouplingSquared * time ^ 2))
      ] direction := by
  rw [fixedActionSelectedTimeAxisAdjointVelocity_gaugePolynomial_normalForm]
  unfold timeAxisGaugeAdjointAlgebraicOperator
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  simp_rw [StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.currentGaussCharge_realSmul_timePrincipal_diracProbe_action_normalForm]
  have iPowThree : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by norm_num [pow_succ]
      _ = -Complex.I := by rw [Complex.I_sq, neg_one_mul]
  fin_cases direction <;>
    simp [
      StageNineP286GaugeConnectionVariationDensity.diracExteriorMotherLieAction_zero_matrix,
      c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three,
      smul_smul, Fin.sum_univ_four, pow_succ] <;>
    simp [diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      diracSpinTwoMatterProbe, diracSpinZeroMatterCoordinate,
      hyperchargeDegreeTwoMatterCoordinate, p286HyperchargeMatterProbe,
      smul_smul, Fin.sum_univ_four]
  all_goals
    ring_nf
    simp [iPowThree, Complex.I_pow_four]
    try ring

/-- On the canonical time axis the primal correction subtracts no caller
trajectory: it is exactly the source-generated matter velocity. -/
theorem fixedActionSelectedTimeAxisMatterCorrection_eq_velocity
    (time : ℝ) :
    completeJointMatterTemporalCoordinateCorrection Source Carry
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        ).matterVelocity := by
  unfold completeJointMatterTemporalCoordinateCorrection
  rw [fixedActionSelectedCarry_matterTemporalDerivative_timeAxis_zero]
  simp

/-- The independent adjoint correction on the same line is likewise exactly
the source-generated adjoint velocity. -/
theorem fixedActionSelectedTimeAxisAdjointCorrection_eq_velocity
    (time : ℝ) :
    completeJointAdjointTemporalCoordinateCorrection Source Carry
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
      matterDualCoordinates
        (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        ).adjointVelocity := by
  unfold completeJointAdjointTemporalCoordinateCorrection
  rw [fixedActionSelectedCarry_adjointTemporalDerivative_timeAxis_zero]
  simp

private theorem matterCorrection_timeLine_coordinatePolynomial :
    (fun time : ℝ =>
      completeJointMatterTemporalCoordinateCorrection Source Carry
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))) =
      fun time : ℝ =>
        (Complex.I * ((5 / 9 : ℝ) *
          c3h181StrongCouplingSquared * time)) •
            matterCoordinateEquiv
              (fun spinIndex =>
                if spinIndex = 3 then p286HyperchargeMatterProbe else 0) +
        (Complex.I * ((5 / 6 : ℝ) *
          c3h181StrongCouplingSquared * time ^ 2)) •
            matterCoordinateEquiv diracSpinTwoMatterProbe := by
  funext time
  rw [fixedActionSelectedTimeAxisMatterCorrection_eq_velocity,
    fixedActionSelectedTimeAxisMatterVelocity_normalForm]
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  funext spinIndex
  fin_cases spinIndex <;> simp [diracSpinTwoMatterProbe]

private theorem intervalIntegral_time_complex (time : ℝ) :
    (∫ candidate : ℝ in 0..time, (candidate : ℂ)) =
      (time ^ 2 / 2 : ℝ) := by
  rw [intervalIntegral.integral_ofReal]
  simpa using (integral_pow (a := (0 : ℝ)) (b := time) 1)

private theorem intervalIntegral_time_sq_complex (time : ℝ) :
    (∫ candidate : ℝ in 0..time, (candidate : ℂ) ^ 2) =
      (time ^ 3 / 3 : ℝ) := by
  rw [show (fun candidate : ℝ => (candidate : ℂ) ^ 2) =
      fun candidate : ℝ => ((candidate ^ 2 : ℝ) : ℂ) by
    funext candidate
    norm_num]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  norm_num

/-- Exact source-native primal primitive on the fixed canonical time axis. -/
theorem fixedActionSelectedTimeAxisMatterPrimitive_normalForm
    (time : ℝ) :
    canonicalTimePrimitive
        (completeJointMatterTemporalCoordinateCorrection Source Carry)
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
      (Complex.I * ((5 / 18 : ℝ) *
        c3h181StrongCouplingSquared * time ^ 2)) •
          matterCoordinateEquiv
            (fun spinIndex =>
              if spinIndex = 3 then p286HyperchargeMatterProbe else 0) +
      (Complex.I * ((5 / 18 : ℝ) *
        c3h181StrongCouplingSquared * time ^ 3)) •
          matterCoordinateEquiv diracSpinTwoMatterProbe := by
  unfold canonicalTimePrimitive
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  rw [matterCorrection_timeLine_coordinatePolynomial]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous fun candidate : ℝ =>
      (Complex.I * ((5 / 9 : ℝ) *
        c3h181StrongCouplingSquared * candidate)) •
          matterCoordinateEquiv
            (fun spinIndex =>
              if spinIndex = 3 then p286HyperchargeMatterProbe else 0)
      ).intervalIntegrable 0 time)
    ((by fun_prop : Continuous fun candidate : ℝ =>
      (Complex.I * ((5 / 6 : ℝ) *
        c3h181StrongCouplingSquared * candidate ^ 2)) •
          matterCoordinateEquiv diracSpinTwoMatterProbe
      ).intervalIntegrable 0 time)]
  simp only [intervalIntegral.integral_smul_const]
  simp [intervalIntegral.integral_const_mul,
    intervalIntegral_time_complex, intervalIntegral_time_sq_complex]
  module

/-- The occupied degree-two coordinate in Dirac spin slot one, exposed only
because the generated adjoint primitive has a physical downstream consumer. -/
def diracSpinOneMatterCoordinate :
    Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun matter := hyperchargeDegreeTwoMatterCoordinate (matter 1)
  map_add' first second := by simp
  map_smul' scalar matter := by simp

private theorem fixedActionSelectedTimeAxisAdjointVelocity_dual_normalForm
    (time : ℝ) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
    ).adjointVelocity =
      (-(Complex.I * ((5 / 6 : ℝ) *
        c3h181StrongCouplingSquared * time ^ 2))) •
          diracSpinZeroMatterCoordinate +
      (-(Complex.I * ((5 / 9 : ℝ) *
        c3h181StrongCouplingSquared * time))) •
          diracSpinOneMatterCoordinate := by
  apply LinearMap.ext
  intro matter
  rw [fixedActionSelectedTimeAxisAdjointVelocity_apply_normalForm]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [show diracSpinZeroMatterCoordinate matter =
      hyperchargeDegreeTwoMatterCoordinate (matter 0) by rfl,
    show diracSpinOneMatterCoordinate matter =
      hyperchargeDegreeTwoMatterCoordinate (matter 1) by rfl]
  ring

private theorem adjointCorrection_timeLine_coordinatePolynomial :
    (fun time : ℝ =>
      completeJointAdjointTemporalCoordinateCorrection Source Carry
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))) =
      fun time : ℝ =>
        (-(Complex.I * ((5 / 6 : ℝ) *
          c3h181StrongCouplingSquared * time ^ 2))) •
            matterDualCoordinates diracSpinZeroMatterCoordinate +
        (-(Complex.I * ((5 / 9 : ℝ) *
          c3h181StrongCouplingSquared * time))) •
            matterDualCoordinates diracSpinOneMatterCoordinate := by
  funext time
  rw [fixedActionSelectedTimeAxisAdjointCorrection_eq_velocity,
    fixedActionSelectedTimeAxisAdjointVelocity_dual_normalForm,
    matterDualCoordinates_add, matterDualCoordinates_smul,
    matterDualCoordinates_smul]

/-- Exact source-native independent-adjoint primitive on that same axis. -/
theorem fixedActionSelectedTimeAxisAdjointPrimitive_normalForm
    (time : ℝ) :
    canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source Carry)
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
      (-(Complex.I * ((5 / 18 : ℝ) *
        c3h181StrongCouplingSquared * time ^ 3))) •
          matterDualCoordinates diracSpinZeroMatterCoordinate +
      (-(Complex.I * ((5 / 18 : ℝ) *
        c3h181StrongCouplingSquared * time ^ 2))) •
          matterDualCoordinates diracSpinOneMatterCoordinate := by
  unfold canonicalTimePrimitive
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  rw [adjointCorrection_timeLine_coordinatePolynomial]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous fun candidate : ℝ =>
      (-(Complex.I * ((5 / 6 : ℝ) *
        c3h181StrongCouplingSquared * candidate ^ 2))) •
          matterDualCoordinates diracSpinZeroMatterCoordinate
      ).intervalIntegrable 0 time)
    ((by fun_prop : Continuous fun candidate : ℝ =>
      (-(Complex.I * ((5 / 9 : ℝ) *
        c3h181StrongCouplingSquared * candidate))) •
          matterDualCoordinates diracSpinOneMatterCoordinate
      ).intervalIntegrable 0 time)]
  simp only [intervalIntegral.integral_smul_const]
  simp [intervalIntegral.integral_const_mul,
    intervalIntegral_time_complex, intervalIntegral_time_sq_complex]
  module

/-! ## Source-native all-point phase pairing of the fixed carry -/

private theorem unitRateFixedInput_gaugeCoordinate_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeConnectionCoordinate UnitRateFixedInput
        (canonicalCauchySlicePoint 0 space) =
      fun direction =>
        if direction = canonicalLorentzianTimeDirection then
          (c3h181StrongCouplingSquared / 6 *
            ∑ axis : Fin 3, (space axis) ^ 2) •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        else 0 := by
  funext direction
  change holonomicP286GaugeConnectionCoordinate
      FixedP506FormNativeJointActionSolvedSuccessor
      (canonicalCauchySlicePoint 0 space) direction = _
  rw [fixedP506FormNativeJointActionSolvedSuccessor_connection_eq_neg_source_neg_point]
  simp only [Pi.neg_apply]
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line]
  fin_cases direction <;>
    simp [c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem unitRateFixedInput_gaugeCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate UnitRateFixedInput 0 = 0 := by
  rw [← canonicalTimeAxis_origin]
  rw [unitRateFixedInput_gaugeCoordinate_zeroSlice_normalForm]
  funext direction
  simp

private theorem unitRateProfile_primalVelocity_origin_zero :
    holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
        UnitRateProfile 0 = 0 := by
  have response := unitRateMatterResponseWrite_profile
    (0 : StageNineSpatialPoint)
  rw [unitRateFixedInput_matterCoordinate_temporalDerivative_zeroSlice_eq_velocityDrift]
    at response
  have writes :=
    fixedP506L0CartanRestartActual_origin_primalAdjointTimeResponseWrites_zero
  rw [writes.1, canonicalTimeAxis_origin] at response
  simpa using response.symm

private theorem unitRateProfile_adjointVelocity_origin_zero :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        UnitRateProfile 0 = 0 := by
  have response := unitRateAdjointResponseWrite_profile
    (0 : StageNineSpatialPoint)
  rw [unitRateProfile_conjugateMatterDerivativeDual_eq_fixedInput] at response
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates at response
  rw [unitRateFixedInput_conjugateMatterCoordinate_temporalDerivative_zeroSlice_eq_velocityDrift]
    at response
  have writes :=
    fixedP506L0CartanRestartActual_origin_primalAdjointTimeResponseWrites_zero
  rw [writes.2, canonicalTimeAxis_origin] at response
  simpa using response.symm

private theorem unitRateGaugeModel_zero_primalVelocity_zero :
    holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
        (UnitRateGaugeModel 0) 0 = 0 := by
  have equality := unitRateProfile_primalVelocity_zeroSlice_eq_gaugeModel
    (0 : StageNineSpatialPoint)
  rw [canonicalTimeAxis_origin,
    unitRateFixedInput_gaugeCoordinate_origin_zero,
    unitRateProfile_primalVelocity_origin_zero] at equality
  exact equality.symm

private theorem unitRateGaugeModel_zero_adjointVelocity_zero :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        (UnitRateGaugeModel 0) 0 = 0 := by
  have equality := unitRateProfile_adjointVelocity_zeroSlice_eq_gaugeModel
    (0 : StageNineSpatialPoint)
  rw [canonicalTimeAxis_origin,
    unitRateFixedInput_gaugeCoordinate_origin_zero,
    unitRateProfile_adjointVelocity_origin_zero] at equality
  exact equality.symm

private theorem unitRateProfile_primalVelocity_zeroSlice_phase_normalForm
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeMatterRawTimeVelocity UnitRateProfile
        (canonicalCauchySlicePoint 0 space) =
      (Complex.I * ((5 / 18 : ℝ) * c3h181StrongCouplingSquared *
        ∑ axis : Fin 3, (space axis) ^ 2)) • diracSpinTwoMatterProbe := by
  apply matterCoordinateEquiv.injective
  have normal :=
    unitRateProfile_primalVelocity_zeroSlice_coordinate_normalForm space
  rw [unitRateGaugeModel_zero_primalVelocity_zero,
    matterCoordinateEquiv.map_zero, zero_add,
    unitRateFixedInput_gaugeCoordinate_zeroSlice_normalForm] at normal
  rw [normal]
  rw [unitRateProfilePrimalGaugeCoordinateCLM_apply,
    unitRateProfilePrimalGaugeCoordinateLinear_apply]
  simp only [canonicalLorentzianTimeDirection, Fin.isValue,
    Fin.succ_ne_zero, ↓reduceIte, p286CoordinateEquiv.symm.map_zero,
    p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix,
    Finset.sum_const_zero, smul_zero, map_zero]
  rw [p286CoordinateEquiv.symm.map_smul,
    p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul,
    LinearMap.smul_apply,
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.currentGaussCharge_spinTwo_action_normalForm]
  rw [show identityCoframeMatterTimePrincipal
      (0 : DiracExteriorMatterCarrier) = 0 by
    simp [StageNineMatterActionTimeVelocity.identityCoframeMatterTimePrincipal]]
  congr 1
  module

private theorem unitRateProfile_adjointVelocity_zeroSlice_phase_normalForm
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        UnitRateProfile (canonicalCauchySlicePoint 0 space) =
      (-(Complex.I * ((5 / 18 : ℝ) * c3h181StrongCouplingSquared *
        ∑ axis : Fin 3, (space axis) ^ 2))) •
          diracSpinZeroMatterCoordinate := by
  let target : Module.Dual ℂ DiracExteriorMatterCarrier :=
    (-(Complex.I * ((5 / 18 : ℝ) * c3h181StrongCouplingSquared *
      ∑ axis : Fin 3, (space axis) ^ 2))) •
        diracSpinZeroMatterCoordinate
  have normal :=
    unitRateProfile_adjointVelocity_zeroSlice_coordinate_normalForm space
  have coordinatesZero :
      matterDualCoordinates
          (0 : Module.Dual ℂ DiracExteriorMatterCarrier) = 0 := by
    apply PiLp.ext
    intro index
    simp [matterDualCoordinates]
  rw [unitRateGaugeModel_zero_adjointVelocity_zero,
    coordinatesZero, zero_add,
    unitRateFixedInput_gaugeCoordinate_zeroSlice_normalForm] at normal
  have gaugeCoordinates :
      unitRateProfileAdjointGaugeCoordinateCLM (fun direction =>
        if direction = canonicalLorentzianTimeDirection then
          (c3h181StrongCouplingSquared / 6 *
            ∑ axis : Fin 3, (space axis) ^ 2) •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        else 0) = matterDualCoordinates target := by
    rw [unitRateProfileAdjointGaugeCoordinateCLM_apply,
      unitRateProfileAdjointGaugeCoordinateLinear_apply]
    apply congrArg matterDualCoordinates
    apply LinearMap.ext
    intro matter
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.sum_apply]
    rw [show canonicalLorentzianTimeDirection = 0 by rfl]
    rw [Fin.sum_univ_four]
    have twoNe : (2 : LorentzianIndex) ≠ 0 := by decide
    have threeNe : (3 : LorentzianIndex) ≠ 0 := by decide
    simp only [Fin.isValue,
      one_ne_zero, twoNe, threeNe, ↓reduceIte,
      p286CoordinateEquiv.symm.map_zero, p286LieBlockEmbed_zero,
      diracExteriorMotherLieAction_zero_matrix, map_zero, add_zero]
    change diracSpinZeroMatterCoordinate
        (identityCoframeMatterPrincipal 0
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                ((c3h181StrongCouplingSquared / 6 *
                  ∑ axis : Fin 3, (space axis) ^ 2) •
                    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
            (identityCoframeMatterPrincipal 0 matter))) = target matter
    rw [StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.currentGaussCharge_realSmul_diracCoordinate_principal_action_normalForm]
    have timeInvolutive :
        identityCoframeMatterPrincipal 0
            (identityCoframeMatterPrincipal 0 matter) = matter := by
      simpa only [canonicalLorentzianTimeDirection] using
        identityCoframeMatterPrincipal_time_involutive matter
    rw [timeInvolutive]
    unfold target
    simp only [LinearMap.smul_apply]
    push_cast
    ring
  calc
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          UnitRateProfile (canonicalCauchySlicePoint 0 space) =
        matterDualOfCoordinates
          (matterDualCoordinates
            (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
              UnitRateProfile (canonicalCauchySlicePoint 0 space))) :=
      (matterDualOfCoordinates_surjective _).symm
    _ = matterDualOfCoordinates (matterDualCoordinates target) := by
      rw [normal, gaugeCoordinates]
    _ = target := matterDualOfCoordinates_surjective target
    _ = _ := rfl

private theorem fixedActionSelectedCarry_matter_allPoint_phase_normalForm
    (time : ℝ) (space : StageNineSpatialPoint) :
    Carry.matter (canonicalCauchySlicePoint time space) =
      ((1 : ℂ) + Complex.I *
        ((5 / 18 : ℝ) * c3h181StrongCouplingSquared * time *
          ∑ axis : Fin 3, (space axis) ^ 2)) •
        diracSpinTwoMatterProbe := by
  apply matterCoordinateEquiv.injective
  rw [carry_matter_slice_affine_normalForm,
    timeAxisPrimalSpatialRateCoordinates_eq_unitRateProfileVelocity,
    unitRateProfile_primalVelocity_zeroSlice_phase_normalForm]
  simp only [map_smul]
  module

private theorem fixedActionSelectedCarry_adjoint_allPoint_phase_normalForm
    (time : ℝ) (space : StageNineSpatialPoint) :
    Carry.conjugateMatter (canonicalCauchySlicePoint time space) =
      ((1 : ℂ) - Complex.I *
        ((5 / 18 : ℝ) * c3h181StrongCouplingSquared * time *
          ∑ axis : Fin 3, (space axis) ^ 2)) •
        diracSpinZeroMatterCoordinate := by
  let target : Module.Dual ℂ DiracExteriorMatterCarrier :=
    ((1 : ℂ) - Complex.I *
      ((5 / 18 : ℝ) * c3h181StrongCouplingSquared * time *
        ∑ axis : Fin 3, (space axis) ^ 2)) •
      diracSpinZeroMatterCoordinate
  have coordinates := carry_conjugateMatter_slice_affine_normalForm time space
  rw [timeAxisAdjointSpatialRateCoordinates_eq_unitRateProfileVelocity,
    unitRateProfile_adjointVelocity_zeroSlice_phase_normalForm,
    matterDualCoordinates_smul] at coordinates
  calc
    Carry.conjugateMatter (canonicalCauchySlicePoint time space) =
        matterDualOfCoordinates
          (matterDualCoordinates
            (Carry.conjugateMatter
              (canonicalCauchySlicePoint time space))) :=
      (matterDualOfCoordinates_surjective _).symm
    _ = matterDualOfCoordinates (matterDualCoordinates target) := by
      congr 1
      change holonomicConjugateMatterCoordinates Carry
          (canonicalCauchySlicePoint time space) = matterDualCoordinates target
      rw [coordinates]
      unfold target
      rw [matterDualCoordinates_smul]
      module
    _ = target := matterDualOfCoordinates_surjective target
    _ = _ := rfl

/-- The all-point carry phase as one canonical P286 coefficient material. -/
private def fixedActionSelectedCarryP286Coefficient
    (time : ℝ) (space : StageNineSpatialPoint) : Fin 4 → ℂ :=
  ![0, 0,
    (1 : ℂ) + Complex.I *
      ((5 / 18 : ℝ) * c3h181StrongCouplingSquared * time *
        ∑ axis : Fin 3, (space axis) ^ 2),
    0]

private theorem fixedActionSelectedCarry_matter_eq_p286SpinMatter
    (time : ℝ) (space : StageNineSpatialPoint) :
    Carry.matter (canonicalCauchySlicePoint time space) =
      p286SpinMatter
        (fixedActionSelectedCarryP286Coefficient time space) := by
  rw [fixedActionSelectedCarry_matter_allPoint_phase_normalForm]
  funext spin
  fin_cases spin <;>
    simp [fixedActionSelectedCarryP286Coefficient, p286SpinMatter,
      diracSpinTwoMatterProbe, add_smul]

private theorem fixedActionSelectedCarryP286Coefficient_star_two
    (time : ℝ) (space : StageNineSpatialPoint) :
    (starRingEnd ℂ)
        (fixedActionSelectedCarryP286Coefficient time space 2) =
      (1 : ℂ) - Complex.I *
        ((5 / 18 : ℝ) * c3h181StrongCouplingSquared * time *
          ∑ axis : Fin 3, (space axis) ^ 2) := by
  simp only [fixedActionSelectedCarryP286Coefficient,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    starRingEnd_apply]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im]

private theorem fixedActionSelectedCarryP286Coefficient_star_zero
    (time : ℝ) (space : StageNineSpatialPoint) :
    (starRingEnd ℂ)
        (fixedActionSelectedCarryP286Coefficient time space 0) = 0 := by
  simp only [fixedActionSelectedCarryP286Coefficient,
    Matrix.cons_val_zero, map_zero]

private theorem fixedActionSelectedCarryP286Coefficient_star_one
    (time : ℝ) (space : StageNineSpatialPoint) :
    (starRingEnd ℂ)
        (fixedActionSelectedCarryP286Coefficient time space 1) = 0 := by
  simp only [fixedActionSelectedCarryP286Coefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_zero]

private theorem fixedActionSelectedCarryP286Coefficient_star_three
    (time : ℝ) (space : StageNineSpatialPoint) :
    (starRingEnd ℂ)
        (fixedActionSelectedCarryP286Coefficient time space 3) = 0 := by
  simp only [fixedActionSelectedCarryP286Coefficient,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_zero]

private theorem p286SpinCoordinate_zero_eq_diracSpinZeroMatterCoordinate :
    p286SpinCoordinate 0 = diracSpinZeroMatterCoordinate := by
  apply LinearMap.ext
  intro matter
  rfl

private theorem fixedActionSelectedCarry_adjoint_eq_p286SpinAdjoint
    (time : ℝ) (space : StageNineSpatialPoint) :
    Carry.conjugateMatter (canonicalCauchySlicePoint time space) =
      p286SpinAdjoint
        (fixedActionSelectedCarryP286Coefficient time space) := by
  rw [fixedActionSelectedCarry_adjoint_allPoint_phase_normalForm]
  unfold p286SpinAdjoint
  rw [fixedActionSelectedCarryP286Coefficient_star_two,
    fixedActionSelectedCarryP286Coefficient_star_zero,
    fixedActionSelectedCarryP286Coefficient_star_one,
    fixedActionSelectedCarryP286Coefficient_star_three,
    p286SpinCoordinate_zero_eq_diracSpinZeroMatterCoordinate]
  simp only [zero_smul, add_zero]

/-- The carry is itself a common P286 primal/adjoint material at every point.
This is stronger than its current-reality readout. -/
theorem fixedActionSelectedCarry_p286DiracPaired
    (time : ℝ) (space : StageNineSpatialPoint) :
    P286DiracPaired
      (Carry.matter (canonicalCauchySlicePoint time space))
      (Carry.conjugateMatter (canonicalCauchySlicePoint time space)) := by
  rw [fixedActionSelectedCarry_matter_eq_p286SpinMatter,
    fixedActionSelectedCarry_adjoint_eq_p286SpinAdjoint]
  exact p286DiracPaired_material _

/-- The fixed source/action carry has one paired P286 phase at every spacetime
point: the primal and independent-adjoint factors are complex conjugates.
Consequently all four Dirac-vector-current coordinates remain real without
accepting a current equation, target field, or reality certificate. -/
theorem fixedActionSelectedCarry_diracVectorCurrent_allPoint_real
    (direction : LorentzianIndex) (time : ℝ)
    (space : StageNineSpatialPoint) :
    (Carry.conjugateMatter (canonicalCauchySlicePoint time space)
      (diracMatrixMatterAction (diracGamma direction)
        (Carry.matter (canonicalCauchySlicePoint time space)))).im = 0 := by
  rw [fixedActionSelectedCarry_matter_allPoint_phase_normalForm,
    fixedActionSelectedCarry_adjoint_allPoint_phase_normalForm]
  simp only [LinearMap.smul_apply, map_smul]
  fin_cases direction <;>
    simp [diracMatrixMatterAction, diracSpinZeroMatterCoordinate,
      diracSpinTwoMatterProbe, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, Complex.mul_im] <;>
    ring_nf
  all_goals simp [← Complex.ofReal_pow]

/-- The exact all-point obstruction left after the fixed carry's
source-native paired P286 phase has been eliminated.  Both temporal
primitives are generated by the same fixed source/action occurrence; this
scalar is a physical readout, not an equation or settlement input. -/
def fixedActionSelectedPrimitiveCrossCurrentImaginary
    (direction : LorentzianIndex) (time : ℝ)
    (space : StageNineSpatialPoint) : ℝ :=
  let point := canonicalCauchySlicePoint time space
  let matterPrimitive := matterCoordinateEquiv.symm
    (canonicalTimePrimitive
      (completeJointMatterTemporalCoordinateCorrection Source Carry) point)
  let adjointPrimitive := matterDualOfCoordinates
    (canonicalTimePrimitive
      (completeJointAdjointTemporalCoordinateCorrection Source Carry) point)
  (Carry.conjugateMatter point
      (diracMatrixMatterAction (diracGamma direction) matterPrimitive) +
    adjointPrimitive
      (diracMatrixMatterAction (diracGamma direction)
        (Carry.matter point)) +
    adjointPrimitive
      (diracMatrixMatterAction (diracGamma direction)
        matterPrimitive)).im

/-! ## Source material mouth for the all-point primitive correction -/

/-- Primal temporal primitive generated from one source/current pair. -/
def sourceGeneratedTemporalPrimitiveMatterAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  let carry :=
    completeJointActionSelectedScalarMomentumCarryActual source current
  matterCoordinateEquiv.symm
    (canonicalTimePrimitive
      (completeJointMatterTemporalCoordinateCorrection source carry) point)

/-- Independent-adjoint temporal primitive generated by the same occurrence. -/
def sourceGeneratedTemporalPrimitiveAdjointAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  let carry :=
    completeJointActionSelectedScalarMomentumCarryActual source current
  matterDualOfCoordinates
    (canonicalTimePrimitive
      (completeJointAdjointTemporalCoordinateCorrection source carry) point)

/-- Exact source material responsibility.  It asks the two generated
primitives to be restrictions of one canonical P286 coefficient carrier; it
does not mention a current zero, contact settlement, equation or target. -/
def SourceGeneratedPrimitiveP286PairAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    P286DiracPaired
      (sourceGeneratedTemporalPrimitiveMatterAt source current point)
      (sourceGeneratedTemporalPrimitiveAdjointAt source current point)

/-- Once the source pays the common-material law, the previously exposed
primitive-cross obstruction vanishes by finite P286--Dirac algebra.  The
vanishing is a consumer, not the calculation mouth. -/
theorem fixedActionSelectedPrimitiveCrossCurrentImaginary_zero_of_pairedMaterial
    (paired : SourceGeneratedPrimitiveP286PairAt
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual) :
    ∀ direction time space,
      fixedActionSelectedPrimitiveCrossCurrentImaginary
        direction time space = 0 := by
  intro direction time space
  unfold fixedActionSelectedPrimitiveCrossCurrentImaginary
  dsimp only
  apply P286DiracPaired.primitiveCross_real
  · exact fixedActionSelectedCarry_p286DiracPaired time space
  · simpa only [SourceGeneratedPrimitiveP286PairAt,
      sourceGeneratedTemporalPrimitiveMatterAt,
      sourceGeneratedTemporalPrimitiveAdjointAt] using
        paired (canonicalCauchySlicePoint time space)

end
end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedDiracVectorCurrentTemporalRateZeroSlice
