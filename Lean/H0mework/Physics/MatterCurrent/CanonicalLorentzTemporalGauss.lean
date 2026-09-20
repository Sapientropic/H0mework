import H0mework.Physics.Cauchy.LorentzActionCauchySplit
import H0mework.Physics.MatterCurrent.CanonicalLorentzTangentSimplicity

/-!
# C3h191: same-actual pure-temporal Lorentz Gauss closure

This module evaluates the independent temporal Lorentz Gauss constraint on
the exact C3h189 actual.  It does not replay the constructor equation:

* C3h190 proves the actual coframe and gravity auxiliary are the constant
  simple pair `(1, II⁺(1))`, so every spatial BF-momentum derivative vanishes;
* the connection, primal matter, and adjoint matter retain their C3h187
  origin provenance, so the previously generated contorsion has the same
  action spin readout;
* the C3h191 structural split then evaluates the temporal EL residual to zero
  in all six internal-bivector directions.

Only the algebraic contorsion re-substitution is producer consistency.  The
final temporal Gauss result is a failure-capable constraint on the same actual
at the same contact.  No branch, event, residual target, whole-field
transporter, supplied equation receipt, or global source-time evolution is
used.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTemporalGauss

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTangentSimplicity
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-- Every BF momentum entering the spatial divergence is a literal constant
function on the same C3h189 local actual. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_BFMomentumEvaluation_constant
    (space : StageNineSpatialPoint)
    (derivativeDirection : LorentzianIndex)
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentum
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space)
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          direction) =
      fun _ =>
        gravityAuxiliaryHodgePairingPolynomial 1
          (physicalIIPlusBivector 1)
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) := by
  funext point
  unfold lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityAuxiliary_simple]
  simp

/-- Hence all three spatial BF-momentum derivatives vanish throughout the
local actual, for every Lorentz one-form test direction. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_spatialBFMomentumDivergence_zero
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionSpatialBFMomentumDivergence
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space)
        direction point =
      0 := by
  unfold lorentzConnectionSpatialBFMomentumDivergence
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_BFMomentumEvaluation_constant,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_BFMomentumEvaluation_constant,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_BFMomentumEvaluation_constant]
  simp [fieldDirectionalDerivative]

/-- The actual installer changes only `B`; its origin gravity connection is
therefore the C3h187 action-generated Einstein--Cartan contorsion. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityConnection_contorsion
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      space).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates :=
  positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_gravityConnection_contorsion
    space

/-- The same actual retains the C3h187 action spin at the contact origin. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_spinCoordinates
    (space : StageNineSpatialPoint) :
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space) 0 =
      positiveP506MatterCurrentEinsteinCartanSpinCoordinates := by
  calc
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space)
          0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual
            space)
          0 := by
      apply actualMatterSpinActionCoordinates_eq_of_origin_fields
      · exact
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one
            space 0).trans
            (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_coframe_one
              space).symm
      · rfl
      · rfl
    _ = positiveP506MatterCurrentEinsteinCartanSpinCoordinates :=
      positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_spinCoordinates
        space

/-- Re-substitution of the generated contorsion on this actual.  This theorem
is producer consistency and is not counted as the independent Gauss closure. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_lorentzAlgebraic_producerConsistency
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space)
        direction 0 =
      0 := by
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors]
  exact actualSimpleBContorsion_algebraicBalance
    positiveSmoothUnifiedSource
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space)
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one
      space 0)
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityAuxiliary_simple
      space 0)
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityConnection_contorsion
      space)
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_spinCoordinates
      space)
    direction

/-- Frontier theorem: all six pure-temporal Lorentz Gauss tests vanish on the
same source-generated C3h189 actual at its canonical contact origin. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_temporalGauss
    (space : StageNineSpatialPoint) :
    CanonicalLorentzTemporalGaussConstraintAt positiveSmoothUnifiedSource
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space) 0 := by
  intro component
  rw [lorentzTemporalGaussResidual_eq_algebraic_sub_spatial,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_lorentzAlgebraic_producerConsistency,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_spatialBFMomentumDivergence_zero]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTemporalGauss
