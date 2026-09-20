import H0mework.Physics.RepairedAction.ActionSpatialSectionRecenterActionJetNaturality
import H0mework.Physics.CartanAction.CartanReactionCurrentRestart
import H0mework.Physics.ScalarJets.ScalarActionSecondJetLocalActualLift

/-!
# Repaired form-native scalar second-jet action response

At one matching fixed P506/L0 contact, the repaired scalar action generates
its required temporal canonical-momentum derivative.  The difference from
the current temporal momentum is lifted through the already faithful finite
real scalar dual and installed as the canonical quadratic time jet.

The producer reads only the source/current action channels.  It accepts no
joint residual, support coordinate, sign choice, target acceleration,
branch, equation witness, or zero-fiber certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterActionJetNaturality
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Dependency-ordered fixed action current -/

/-- Matching P506/L0 contact after the Cartan restart and the repaired
matter/constitutive writes, but before scalar, P286, and final EC settlement. -/
def recenteredCartanRepairedConstitutiveCurrent
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedConstitutiveWrittenCurrent
    positiveSmoothUnifiedSource
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource
      (spatiallyRecenterHolonomicConfiguration
        FixedP506FormNativeJointActionSolvedSuccessor space))

@[simp] theorem recenteredCartanRepairedConstitutiveCurrent_coframe
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).coframe =
      (recenteredContactActual space).coframe :=
  rfl

@[simp] theorem recenteredCartanRepairedConstitutiveCurrent_gaugeConnection
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).gaugeConnection =
      (recenteredContactActual space).gaugeConnection :=
  rfl

@[simp] theorem recenteredCartanRepairedConstitutiveCurrent_scalar
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).scalar =
      (recenteredContactActual space).scalar :=
  rfl

private theorem
    recenteredCartanRepairedConstitutiveCurrent_scalarCovariantDerivative_eq
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        (recenteredCartanRepairedConstitutiveCurrent space) =
      holonomicScalarCovariantDerivative (recenteredContactActual space) := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [recenteredCartanRepairedConstitutiveCurrent_gaugeConnection,
    recenteredCartanRepairedConstitutiveCurrent_scalar]

private theorem
    recenteredCartanRepairedConstitutiveCurrent_scalarDifferentialMomentum_eq
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) direction
        derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredContactActual space) direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [recenteredCartanRepairedConstitutiveCurrent_coframe,
    recenteredCartanRepairedConstitutiveCurrent_scalarCovariantDerivative_eq]

theorem
    recenteredCartanRepairedConstitutiveCurrent_scalarDifferentialMomentum_contDiffAt_origin
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) direction
        derivativeDirection)
      0 := by
  rw [
    recenteredCartanRepairedConstitutiveCurrent_scalarDifferentialMomentum_eq]
  exact
    recenteredContactScalarDifferentialMomentum_contDiffAt_origin
      space direction derivativeDirection

/-! ## Repaired action-owned temporal demand -/

def recenteredContactScalarCurrentPdot
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  fieldDirectionalDerivative
    (scalarDifferentialMomentum positiveSmoothUnifiedSource
      (recenteredCartanRepairedConstitutiveCurrent space) direction
      canonicalLorentzianTimeDirection)
    0 canonicalLorentzianTimeDirection

def recenteredContactScalarSpatialMomentumDivergence
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  ∑ derivativeDirection : Fin 3,
    fieldDirectionalDerivative
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) direction
        derivativeDirection.succ)
      0 derivativeDirection.succ

/-- Forward `3+1` Hamilton equation generated by the repaired scalar action. -/
def recenteredContactDiracDualScalarRequiredPdot
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  diracDualScalarAlgebraicDirectionalCoefficient
      positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) direction 0 -
    recenteredContactScalarSpatialMomentumDivergence space direction

/-- Action-generated Legendre demand.  This is assembled before any scalar
Euler residual carrier is read. -/
def recenteredContactDiracDualScalarTemporalDemand
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  recenteredContactDiracDualScalarRequiredPdot space direction -
    recenteredContactScalarCurrentPdot space direction

/-! ## Real linearity of the repaired action demand -/

private theorem scalarVariationDifferentialDirection_add
    (first second : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarVariationDifferentialDirection (first + second)
        derivativeDirection =
      scalarVariationDifferentialDirection first derivativeDirection +
        scalarVariationDifferentialDirection second derivativeDirection := by
  funext formDirection
  by_cases same : formDirection = derivativeDirection <;>
    simp [scalarVariationDifferentialDirection, same]

private theorem scalarVariationDifferentialDirection_real_smul
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarVariationDifferentialDirection (parameter • direction)
        derivativeDirection =
      parameter •
        scalarVariationDifferentialDirection direction derivativeDirection := by
  funext formDirection
  simp [scalarVariationDifferentialDirection]

private theorem holonomicScalarVariationAlgebraicDirection_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : ScalarCoordinateCarrier)
    (point : BasePoint) :
    holonomicScalarVariationAlgebraicDirection configuration (first + second)
        point =
      holonomicScalarVariationAlgebraicDirection configuration first point +
        holonomicScalarVariationAlgebraicDirection configuration second point := by
  funext formDirection
  unfold holonomicScalarVariationAlgebraicDirection
  exact scalarMotherLieAction_add_right _ _ _

private theorem holonomicScalarVariationAlgebraicDirection_real_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    holonomicScalarVariationAlgebraicDirection configuration
        (parameter • direction) point =
      parameter •
        holonomicScalarVariationAlgebraicDirection configuration direction
          point := by
  funext formDirection
  unfold holonomicScalarVariationAlgebraicDirection
  exact scalarMotherLieAction_real_smul_right _ _ _

private theorem scalarPotentialFirstVariation_add
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (first second : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation source field (first + second) =
      scalarPotentialFirstVariation source field first +
        scalarPotentialFirstVariation source field second := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change
    2 * scalarCoordinatePairingRe
        (field.scalar - sourceGeneratedVacuumCoordinates source)
        (first + second) =
      2 * scalarCoordinatePairingRe
          (field.scalar - sourceGeneratedVacuumCoordinates source) first +
        2 * scalarCoordinatePairingRe
          (field.scalar - sourceGeneratedVacuumCoordinates source) second
  rw [scalarCoordinatePairingRe_add_right]
  ring

private theorem diracDualScalarYukawaFirstVariationDensity_add
    (field : StageNineContinuumPointField)
    (first second : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity field (first + second) =
      diracDualScalarYukawaFirstVariationDensity field first +
        diracDualScalarYukawaFirstVariationDensity field second := by
  unfold diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  rw [scalarCoordinateEquiv.symm.map_add,
    diracDualRightChiralYukawaAction_add, LinearMap.add_apply, map_add]
  exact Complex.add_re _ _

private theorem scalarDifferentialMomentum_add
    (space : StageNineSpatialPoint)
    (first second : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) (first + second)
        derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) first
          derivativeDirection +
        scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) second
          derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
  rw [scalarVariationDifferentialDirection_add,
    scalarKineticFirstVariationDensity_add]
  simp only [Pi.add_apply]
  ring

private theorem scalarDifferentialMomentum_real_smul
    (space : StageNineSpatialPoint)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space)
        (parameter • direction)
        derivativeDirection =
      parameter •
        scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) direction
          derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
  rw [scalarVariationDifferentialDirection_real_smul,
    scalarKineticFirstVariationDensity_real_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem diracDualScalarAlgebraicDirectionalCoefficient_add
    (space : StageNineSpatialPoint)
    (first second : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space)
        (first + second) 0 =
      diracDualScalarAlgebraicDirectionalCoefficient
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) first 0 +
        diracDualScalarAlgebraicDirectionalCoefficient
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) second
          0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [holonomicScalarVariationAlgebraicDirection_add,
    scalarKineticFirstVariationDensity_add,
    scalarPotentialFirstVariation_add,
    diracDualScalarYukawaFirstVariationDensity_add]
  ring

private theorem diracDualScalarAlgebraicDirectionalCoefficient_real_smul
    (space : StageNineSpatialPoint)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space)
        (parameter • direction) 0 =
      parameter *
        diracDualScalarAlgebraicDirectionalCoefficient
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space)
          direction 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [holonomicScalarVariationAlgebraicDirection_real_smul,
    scalarKineticFirstVariationDensity_real_smul,
    scalarPotentialFirstVariation_real_smul,
    diracDualScalarYukawaFirstVariationDensity_real_smul]
  ring

private theorem recenteredContactScalarMomentumDirectionalDerivative_add
    (space : StageNineSpatialPoint)
    (first second : ScalarCoordinateCarrier)
    (momentumDirection derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) (first + second)
          momentumDirection)
        0 derivativeDirection =
      fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            (recenteredCartanRepairedConstitutiveCurrent space) first
            momentumDirection)
          0 derivativeDirection +
        fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            (recenteredCartanRepairedConstitutiveCurrent space) second
            momentumDirection)
          0 derivativeDirection := by
  have firstDifferentiable : DifferentiableAt ℝ
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) first
        momentumDirection) 0 :=
    (recenteredCartanRepairedConstitutiveCurrent_scalarDifferentialMomentum_contDiffAt_origin
      space first momentumDirection).differentiableAt (by simp)
  have secondDifferentiable : DifferentiableAt ℝ
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) second
        momentumDirection) 0 :=
    (recenteredCartanRepairedConstitutiveCurrent_scalarDifferentialMomentum_contDiffAt_origin
      space second momentumDirection).differentiableAt (by simp)
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_add,
    fderiv_add firstDifferentiable secondDifferentiable, add_apply]

private theorem
    recenteredContactScalarMomentumDirectionalDerivative_real_smul
    (space : StageNineSpatialPoint)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (momentumDirection derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space)
          (parameter • direction)
          momentumDirection)
        0 derivativeDirection =
      parameter *
        fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            (recenteredCartanRepairedConstitutiveCurrent space) direction
            momentumDirection)
          0 derivativeDirection := by
  have differentiable : DifferentiableAt ℝ
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) direction
        momentumDirection) 0 :=
    (recenteredCartanRepairedConstitutiveCurrent_scalarDifferentialMomentum_contDiffAt_origin
      space direction momentumDirection).differentiableAt (by simp)
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_real_smul]
  change
    (fderiv ℝ
      (fun point => parameter *
        scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) direction
          momentumDirection point)
      0) (coordinateDirection derivativeDirection) = _
  rw [fderiv_const_mul differentiable parameter]
  rfl

private theorem recenteredContactScalarCurrentPdot_add
    (space : StageNineSpatialPoint)
    (first second : ScalarCoordinateCarrier) :
    recenteredContactScalarCurrentPdot space (first + second) =
      recenteredContactScalarCurrentPdot space first +
        recenteredContactScalarCurrentPdot space second := by
  unfold recenteredContactScalarCurrentPdot
  exact recenteredContactScalarMomentumDirectionalDerivative_add
    space first second canonicalLorentzianTimeDirection
      canonicalLorentzianTimeDirection

private theorem recenteredContactScalarCurrentPdot_real_smul
    (space : StageNineSpatialPoint)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier) :
    recenteredContactScalarCurrentPdot space (parameter • direction) =
      parameter * recenteredContactScalarCurrentPdot space direction := by
  unfold recenteredContactScalarCurrentPdot
  exact recenteredContactScalarMomentumDirectionalDerivative_real_smul
    space parameter direction canonicalLorentzianTimeDirection
      canonicalLorentzianTimeDirection

private theorem recenteredContactScalarSpatialMomentumDivergence_add
    (space : StageNineSpatialPoint)
    (first second : ScalarCoordinateCarrier) :
    recenteredContactScalarSpatialMomentumDivergence space (first + second) =
      recenteredContactScalarSpatialMomentumDivergence space first +
        recenteredContactScalarSpatialMomentumDivergence space second := by
  unfold recenteredContactScalarSpatialMomentumDivergence
  simp_rw [recenteredContactScalarMomentumDirectionalDerivative_add]
  exact Finset.sum_add_distrib

private theorem
    recenteredContactScalarSpatialMomentumDivergence_real_smul
    (space : StageNineSpatialPoint)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier) :
    recenteredContactScalarSpatialMomentumDivergence space
        (parameter • direction) =
      parameter *
        recenteredContactScalarSpatialMomentumDivergence space direction := by
  unfold recenteredContactScalarSpatialMomentumDivergence
  simp_rw [recenteredContactScalarMomentumDirectionalDerivative_real_smul]
  exact (Finset.mul_sum _ _ _).symm

private theorem recenteredContactDiracDualScalarRequiredPdot_add
    (space : StageNineSpatialPoint)
    (first second : ScalarCoordinateCarrier) :
    recenteredContactDiracDualScalarRequiredPdot space (first + second) =
      recenteredContactDiracDualScalarRequiredPdot space first +
        recenteredContactDiracDualScalarRequiredPdot space second := by
  unfold recenteredContactDiracDualScalarRequiredPdot
  rw [diracDualScalarAlgebraicDirectionalCoefficient_add,
    recenteredContactScalarSpatialMomentumDivergence_add]
  ring

private theorem recenteredContactDiracDualScalarRequiredPdot_real_smul
    (space : StageNineSpatialPoint)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier) :
    recenteredContactDiracDualScalarRequiredPdot space
        (parameter • direction) =
      parameter *
        recenteredContactDiracDualScalarRequiredPdot space direction := by
  unfold recenteredContactDiracDualScalarRequiredPdot
  rw [diracDualScalarAlgebraicDirectionalCoefficient_real_smul,
    recenteredContactScalarSpatialMomentumDivergence_real_smul]
  ring

private theorem recenteredContactDiracDualScalarTemporalDemand_add
    (space : StageNineSpatialPoint)
    (first second : ScalarCoordinateCarrier) :
    recenteredContactDiracDualScalarTemporalDemand space (first + second) =
      recenteredContactDiracDualScalarTemporalDemand space first +
        recenteredContactDiracDualScalarTemporalDemand space second := by
  unfold recenteredContactDiracDualScalarTemporalDemand
  rw [recenteredContactDiracDualScalarRequiredPdot_add,
    recenteredContactScalarCurrentPdot_add]
  ring

private theorem recenteredContactDiracDualScalarTemporalDemand_real_smul
    (space : StageNineSpatialPoint)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier) :
    recenteredContactDiracDualScalarTemporalDemand space
        (parameter • direction) =
      parameter *
        recenteredContactDiracDualScalarTemporalDemand space direction := by
  unfold recenteredContactDiracDualScalarTemporalDemand
  rw [recenteredContactDiracDualScalarRequiredPdot_real_smul,
    recenteredContactScalarCurrentPdot_real_smul]
  ring

/-- The repaired mother action's scalar temporal demand as a genuine real
continuous dual on the fixed finite scalar carrier. -/
def recenteredContactDiracDualScalarTemporalDemandDual
    (space : StageNineSpatialPoint) :
    Module.Dual ℝ ScalarCoordinateCarrier where
  toFun := recenteredContactDiracDualScalarTemporalDemand space
  map_add' := recenteredContactDiracDualScalarTemporalDemand_add space
  map_smul' := by
    intro parameter direction
    simpa only [RingHom.id_apply, smul_eq_mul] using
      recenteredContactDiracDualScalarTemporalDemand_real_smul
        space parameter direction

/-- Unique no-free-parameter scalar acceleration reconstructed from the
action-generated temporal demand. -/
def recenteredContactDiracDualScalarAcceleration
    (space : StageNineSpatialPoint) : ScalarCoordinateCarrier :=
  -scalarActionRealDual
    (recenteredContactDiracDualScalarTemporalDemandDual space)

theorem recenteredContactDiracDualScalarAcceleration_actionLaw
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    recenteredContactDiracDualScalarTemporalDemand space direction =
      -scalarCoordinatePairingRe direction
        (recenteredContactDiracDualScalarAcceleration space) := by
  change
    recenteredContactDiracDualScalarTemporalDemandDual space direction =
      -scalarCoordinatePairingRe direction
        (-scalarActionRealDual
          (recenteredContactDiracDualScalarTemporalDemandDual space))
  rw [show
    scalarCoordinatePairingRe direction
        (-scalarActionRealDual
          (recenteredContactDiracDualScalarTemporalDemandDual space)) =
      -scalarCoordinatePairingRe direction
        (scalarActionRealDual
          (recenteredContactDiracDualScalarTemporalDemandDual space)) by
    change
      scalarCoordinatePairingReBilinear direction
          (-scalarActionRealDual
            (recenteredContactDiracDualScalarTemporalDemandDual space)) =
        -scalarCoordinatePairingReBilinear direction
          (scalarActionRealDual
            (recenteredContactDiracDualScalarTemporalDemandDual space))
    exact map_neg
      (scalarCoordinatePairingReBilinear direction)
      (scalarActionRealDual
        (recenteredContactDiracDualScalarTemporalDemandDual space))]
  rw [neg_neg, scalarCoordinatePairingRe_actionRealDual]

/-! ## Canonical quadratic scalar writer -/

def installScalarQuadraticTimeCorrection
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    StageNineHolonomicConfiguration :=
  { current with
    scalar := fun point =>
      current.scalar point +
        scalarQuadraticTimeCorrection acceleration point }

@[simp] theorem installScalarQuadraticTimeCorrection_coframe
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration).coframe =
      current.coframe :=
  rfl

@[simp] theorem installScalarQuadraticTimeCorrection_gravityConnection
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration
      ).gravityConnection = current.gravityConnection :=
  rfl

@[simp] theorem installScalarQuadraticTimeCorrection_gravityAuxiliary
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration
      ).gravityAuxiliary = current.gravityAuxiliary :=
  rfl

@[simp] theorem installScalarQuadraticTimeCorrection_multiplier
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration
      ).gravitySimplicityMultiplier = current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem installScalarQuadraticTimeCorrection_gaugeConnection
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration
      ).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem installScalarQuadraticTimeCorrection_gaugeAuxiliary
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration
      ).gaugeAuxiliary = current.gaugeAuxiliary :=
  rfl

@[simp] theorem installScalarQuadraticTimeCorrection_matter
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration).matter =
      current.matter :=
  rfl

@[simp] theorem installScalarQuadraticTimeCorrection_conjugateMatter
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration
      ).conjugateMatter = current.conjugateMatter :=
  rfl

@[simp] theorem scalarQuadraticTimeCorrection_firstDerivative_origin
    (acceleration : ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarQuadraticTimeCorrection acceleration) 0 direction = 0 := by
  have derivative :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt (0 : BasePoint)).smul_const
      acceleration
  unfold fieldDirectionalDerivative scalarQuadraticTimeCorrection
  rw [derivative.fderiv]
  simp [coordinateDirection]

@[simp] theorem installScalarQuadraticTimeCorrection_scalar_origin
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier) :
    (installScalarQuadraticTimeCorrection current acceleration).scalar 0 =
      current.scalar 0 := by
  simp [installScalarQuadraticTimeCorrection]

theorem fieldDirectionalDerivative_installScalarQuadraticTimeCorrection_origin
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier)
    (scalarDifferentiable : DifferentiableAt ℝ current.scalar 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (installScalarQuadraticTimeCorrection current acceleration).scalar
        0 direction =
      fieldDirectionalDerivative current.scalar 0 direction := by
  have correctionDifferentiable : DifferentiableAt ℝ
      (scalarQuadraticTimeCorrection acceleration) 0 :=
    ((scalarQuadraticTimeCoefficient_hasFDerivAt (0 : BasePoint)).smul_const
      acceleration).differentiableAt
  unfold installScalarQuadraticTimeCorrection fieldDirectionalDerivative
  change
    (fderiv ℝ
        (current.scalar + scalarQuadraticTimeCorrection acceleration) 0)
        (coordinateDirection direction) =
      (fderiv ℝ current.scalar 0) (coordinateDirection direction)
  rw [fderiv_add scalarDifferentiable correctionDifferentiable, add_apply]
  rw [show
    (fderiv ℝ (scalarQuadraticTimeCorrection acceleration) 0)
        (coordinateDirection direction) = 0 by
      exact scalarQuadraticTimeCorrection_firstDerivative_origin
        acceleration direction]
  exact add_zero _

theorem
    holonomicScalarCovariantDerivative_installScalarQuadraticTimeCorrection_origin
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier)
    (scalarDifferentiable : DifferentiableAt ℝ current.scalar 0) :
    holonomicScalarCovariantDerivative
        (installScalarQuadraticTimeCorrection current acceleration) 0 =
      holonomicScalarCovariantDerivative current 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [fieldDirectionalDerivative_installScalarQuadraticTimeCorrection_origin
    current acceleration scalarDifferentiable direction]
  simp [installScalarQuadraticTimeCorrection]

theorem toContinuumPointField_installScalarQuadraticTimeCorrection_origin
    (current : StageNineHolonomicConfiguration)
    (acceleration : ScalarCoordinateCarrier)
    (scalarDifferentiable : DifferentiableAt ℝ current.scalar 0) :
    toContinuumPointField
        (installScalarQuadraticTimeCorrection current acceleration) 0 =
      toContinuumPointField current 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact installScalarQuadraticTimeCorrection_scalar_origin current acceleration
  · exact
      holonomicScalarCovariantDerivative_installScalarQuadraticTimeCorrection_origin
        current acceleration scalarDifferentiable
  · rfl
  · rfl
  · rfl

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
