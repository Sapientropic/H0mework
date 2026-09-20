import H0mework.Physics.GravityTail.FixedActionJetNaturality
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorCoframeReadback

/-!
# Zero-slice support of the action-selected gravity tail

The gravity-tail occurrence has already emitted one global actual.  This
module compares only the residual projections whose complete primitive
dependency is retained from its action-selected coupled input.  It never
uses a residual coordinate, support branch, or zero-fiber witness to define
an output.

On the canonical zero slice, five of the nine residual coordinates are
settled.  The whole zero-fiber question is therefore equivalent to the four
connection-sensitive reads of this same emitted actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailZeroSliceSupport

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailActionJetNaturality
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorCoframeReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorScalarReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorStructuralReduction
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECP286AllPointSettlement
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Radial : StageNineHolonomicConfiguration :=
  completeJointActionSelectedRadialConnectionActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathActionSelectedJointSuccessor

private abbrev Point (space : StageNineSpatialPoint) : BasePoint :=
  canonicalCauchySlicePoint 0 space

private theorem final_coframe_eq_coupled :
    Final.coframe = Coupled.coframe := by
  calc
    Final.coframe = fun _ => (1 : LorentzianCoframe) :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one
    _ = Successor.coframe := successor_coframe_eq_one.symm
    _ = Coupled.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
        Source Coupled

private theorem final_gaugeConnection_eq_coupled :
    Final.gaugeConnection = Coupled.gaugeConnection := by
  change
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator
      Source Coupled).gaugeConnection = Coupled.gaugeConnection
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gaugeConnection
      Source Coupled

private theorem final_gaugeAuxiliary_eq_coupled :
    Final.gaugeAuxiliary = Coupled.gaugeAuxiliary := by
  change
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator
      Source Coupled).gaugeAuxiliary = Coupled.gaugeAuxiliary
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gaugeAuxiliary
      Source Coupled

private theorem final_scalar_eq_coupled : Final.scalar = Coupled.scalar := by
  change
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator
      Source Coupled).scalar = Coupled.scalar
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_scalar
      Source Coupled

private theorem final_matter_eq_coupled : Final.matter = Coupled.matter := by
  change
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator
      Source Coupled).matter = Coupled.matter
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_matter
      Source Coupled

private theorem final_conjugateMatter_eq_coupled :
    Final.conjugateMatter = Coupled.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator
      Source Coupled).conjugateMatter = Coupled.conjugateMatter
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_conjugateMatter
      Source Coupled

private theorem coupled_gaugeAuxiliary_eq_constitutive :
    Coupled.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source Coupled := by
  funext point
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Radial.coframe point) (holonomicGaugeCurvature Radial point) =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Coupled.coframe point) (holonomicGaugeCurvature Coupled point)
  have coframeEq : Coupled.coframe = Radial.coframe := by rfl
  have connectionEq : Coupled.gaugeConnection = Radial.gaugeConnection := by
    rfl
  rw [congrFun coframeEq point]
  rw [holonomicGaugeCurvature_eq_of_connection_eq Coupled Radial
    connectionEq point]

/-- The constitutive P286 auxiliary remains settled at every spacetime
point of the emitted gravity-tail actual. -/
theorem fixedP506L0ActionSelectedGravityTail_p286GaugeAuxiliaryResidual_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point
      ).p286GaugeAuxiliary = 0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField Final point) = 0
  apply
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField Final point)).2
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField Final point)
      (fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_nondegenerate
        point)).2
  change
    Final.gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Final.coframe point) (holonomicGaugeCurvature Final point)
  rw [congrFun final_gaugeAuxiliary_eq_coupled point,
    congrFun final_coframe_eq_coupled point,
    holonomicGaugeCurvature_eq_of_connection_eq Final Coupled
      final_gaugeConnection_eq_coupled point]
  exact congrFun coupled_gaugeAuxiliary_eq_constitutive point

private theorem final_p286EulerThreeForm_eq_coupled :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Final =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Coupled := by
  apply holonomicFormNativeP286GaugeEulerThreeForm_eq_of_primitiveFields
  · exact final_coframe_eq_coupled
  · exact final_gaugeConnection_eq_coupled
  · exact final_gaugeAuxiliary_eq_coupled
  · exact final_scalar_eq_coupled
  · exact final_matter_eq_coupled
  · exact final_conjugateMatter_eq_coupled

/-- Whole-spacetime P286 connection custody: the gravity-tail occurrence
retains every primitive field read by the P286 Euler three-form from its
already generated coupled input. -/
theorem fixedP506L0ActionSelectedGravityTail_p286GaugeConnectionResidual_eq_coupled
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point
      ).p286GaugeConnection =
      (diracDualFormNativePointwiseJointResidual Source Coupled point
        ).p286GaugeConnection := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Final point =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Coupled point
  exact congrFun final_p286EulerThreeForm_eq_coupled point

/-- The complete P286 connection equation stays closed on the canonical
zero slice because the gravity-only continuation retains every primitive
field read by that equation. -/
theorem fixedP506L0ActionSelectedGravityTail_p286GaugeConnectionResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Final
      (Point space)).p286GaugeConnection = 0 := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Final
      (Point space) = 0
  rw [congrFun final_p286EulerThreeForm_eq_coupled (Point space)]
  have old := successor_p286EulerThreeForm_zeroSlice space
  rw [congrFun successor_p286EulerThreeForm_eq_actionSelectedCoupled
    (Point space)] at old
  exact old

private theorem final_scalarCovariantDerivative_eq_coupled :
    holonomicScalarCovariantDerivative Final =
      holonomicScalarCovariantDerivative Coupled := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [final_scalar_eq_coupled, final_gaugeConnection_eq_coupled]

private theorem final_scalarDifferentialMomentum_eq_coupled
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum Source Final direction derivativeDirection =
      scalarDifferentialMomentum Source Coupled direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_coupled,
    final_scalarCovariantDerivative_eq_coupled]

private theorem final_scalarMomentumDivergence_eq_coupled
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source Final direction =
      scalarDifferentialMomentumDivergence Source Coupled direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [final_scalarDifferentialMomentum_eq_coupled direction]

private theorem final_scalarAlgebraic_eq_coupled
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient Source Final direction
        point =
      diracDualScalarAlgebraicDirectionalCoefficient Source Coupled direction
        point := by
  have variationEq :
      holonomicScalarVariationAlgebraicDirection Final direction point =
        holonomicScalarVariationAlgebraicDirection Coupled direction point := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [final_gaugeConnection_eq_coupled]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_coupled, final_scalar_eq_coupled,
    final_scalarCovariantDerivative_eq_coupled,
    final_matter_eq_coupled, final_conjugateMatter_eq_coupled,
    variationEq]

private theorem final_scalarEuler_eq_coupled
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Final direction
        point =
      diracDualScalarEulerLagrangeDirectionalCoefficient Source Coupled
        direction point := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [final_scalarAlgebraic_eq_coupled,
    congrFun (final_scalarMomentumDivergence_eq_coupled direction) point]

/-- Whole-spacetime scalar custody for the same emitted gravity-tail actual.
The gravity-only continuation changes none of the scalar Euler dependencies. -/
theorem fixedP506L0ActionSelectedGravityTail_scalarResidual_eq_coupled
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point).scalar =
      (diracDualFormNativePointwiseJointResidual Source Coupled point).scalar := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Final direction
        point =
      diracDualScalarEulerLagrangeDirectionalCoefficient Source Coupled
        direction point
  exact final_scalarEuler_eq_coupled direction point

/-- The scalar equation remains settled on the canonical zero slice.  This
is a retained-dependency readback, not a new scalar writer. -/
theorem fixedP506L0ActionSelectedGravityTail_scalarResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Final
      (Point space)).scalar = 0 := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Final direction
      (Point space) = 0
  rw [final_scalarEuler_eq_coupled]
  exact actionSelectedCoupled_scalarEuler_zeroSlice space direction

/-- Exact support classification on the same emitted actual.  The complete
zero-fiber question contains only the four reads genuinely reopened by the
gravity-tail connection and live multiplier. -/
theorem
    fixedP506L0ActionSelectedGravityTail_zeroSlice_residual_eq_zero_iff_connectionSensitiveReads_zero
    (space : StageNineSpatialPoint) :
    diracDualFormNativePointwiseJointResidual Source Final (Point space) = 0 ↔
      (diracDualFormNativePointwiseJointResidual Source Final
          (Point space)).lorentzConnection = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Final
          (Point space)).matter = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Final
          (Point space)).conjugateMatter = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Final
          (Point space)).coframe = 0 := by
  constructor
  · intro residualZero
    exact
      ⟨congrArg
          DiracDualFormNativePointwiseJointResidualCarrier.lorentzConnection
          residualZero,
        congrArg DiracDualFormNativePointwiseJointResidualCarrier.matter
          residualZero,
        congrArg
          DiracDualFormNativePointwiseJointResidualCarrier.conjugateMatter
          residualZero,
        congrArg DiracDualFormNativePointwiseJointResidualCarrier.coframe
          residualZero⟩
  · rintro ⟨lorentzConnection, matter, conjugateMatter, coframe⟩
    apply DiracDualFormNativePointwiseJointResidualCarrier.ext
    · exact
        fixedP506L0ActionSelectedGravityTail_gravityMultiplierResidual_zero
          (Point space)
    · exact
        fixedP506L0ActionSelectedGravityTail_gravityAuxiliaryResidual_zero
          (Point space)
    · exact
        fixedP506L0ActionSelectedGravityTail_p286GaugeAuxiliaryResidual_zero
          (Point space)
    · exact lorentzConnection
    · exact
        fixedP506L0ActionSelectedGravityTail_p286GaugeConnectionResidual_zeroSlice
          space
    · exact fixedP506L0ActionSelectedGravityTail_scalarResidual_zeroSlice space
    · exact matter
    · exact conjugateMatter
    · exact coframe

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailZeroSliceSupport
