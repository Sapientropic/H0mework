import H0mework.Physics.ConstrainedCauchy.LocalActualLift
import H0mework.Physics.DualVariation.JointResidualCarrier

/-!
# Matter/scalar reads across the full Einstein--Cartan Cauchy write

The full Einstein--Cartan Cauchy producer changes the Lorentz connection and
the two gravity reaction fields while retaining the coframe, gauge fields,
scalar, matter, and conjugate matter.

This module records the exact consequence for the three matter/scalar Euler
readers at an arbitrary spacetime occurrence:

* the scalar reader is preserved unconditionally;
* the primal and adjoint matter readers are preserved whenever the written
  Lorentz connection has the same value at that occurrence.

The latter hypothesis is an explicit read-after-write seam, not a supplied
equation or zero-fiber receipt.  These are transport theorems; they do not
claim that the Cauchy write preserves the Lorentz connection away from its
anchored contact.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECFullCauchyMatterScalarReadTransport

open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterVariation
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineP286GaugeConnectionActionVariation
open StageNineScalarPointwiseEquation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Written
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current

private theorem written_scalarCovariantDerivative_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicScalarCovariantDerivative (Written source current) =
      holonomicScalarCovariantDerivative current := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]

private theorem written_scalarDifferentialMomentum_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source (Written source current) direction
        derivativeDirection =
      scalarDifferentialMomentum source current direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    written_scalarCovariantDerivative_eq]

private theorem written_scalarDifferentialMomentumDivergence_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence source (Written source current)
        direction =
      scalarDifferentialMomentumDivergence source current direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [written_scalarDifferentialMomentum_eq]

private theorem written_scalarAlgebraic_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient source
        (Written source current) direction point =
      diracDualScalarAlgebraicDirectionalCoefficient source current
        direction point := by
  have variationEquality :
      holonomicScalarVariationAlgebraicDirection
          (Written source current) direction point =
        holonomicScalarVariationAlgebraicDirection current direction point := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    written_scalarCovariantDerivative_eq,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    variationEquality]

/-- The scalar Euler reader is globally insensitive to the gravity-only
fields changed by the full Einstein--Cartan Cauchy write. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalarResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (Written source current) point).scalar =
      (diracDualFormNativePointwiseJointResidual source current point).scalar := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (Written source current) direction point =
      diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction point
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [written_scalarAlgebraic_eq,
    congrFun
      (written_scalarDifferentialMomentumDivergence_eq source current
        direction)
      point]

private theorem written_matterDifferentialMomentum_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source (Written source current) direction
        derivativeDirection =
      matterDifferentialMomentum source current direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter]

private theorem written_matterDifferentialMomentumDivergence_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence source (Written source current)
        direction =
      matterDifferentialMomentumDivergence source current direction := by
  funext point
  unfold matterDifferentialMomentumDivergence
  simp_rw [written_matterDifferentialMomentum_eq]

private theorem written_matterAlgebraic_eq_of_connection_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint)
    (connectionEquality :
      (Written source current).gravityConnection point =
        current.gravityConnection point) :
    diracDualMatterAlgebraicDirectionalCoefficient source
        (Written source current) direction point =
      diracDualMatterAlgebraicDirectionalCoefficient source current direction
        point := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection
          (Written source current) direction point =
        holonomicMatterVariationAlgebraicDirection current direction point := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [connectionEquality,
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    variationEquality]

/-- The primal matter reader crosses the full EC write exactly at occurrences
where the Lorentz-connection value is preserved.  The differential momentum
part is already preserved globally; the stated equality is the only local
read-after-write seam. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matterResidual_eq_current_of_connection_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (connectionEquality :
      (Written source current).gravityConnection point =
        current.gravityConnection point) :
    (diracDualFormNativePointwiseJointResidual source
      (Written source current) point).matter =
      (diracDualFormNativePointwiseJointResidual source current point).matter := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient source
        (Written source current) direction point =
      diracDualMatterEulerLagrangeDirectionalCoefficient source current
        direction point
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [written_matterAlgebraic_eq_of_connection_eq source current direction
      point connectionEquality,
    congrFun
      (written_matterDifferentialMomentumDivergence_eq source current
        direction)
      point]

private theorem written_matterCovariantDerivative_at_eq_of_connection_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (connectionEquality :
      (Written source current).gravityConnection point =
        current.gravityConnection point) :
    holonomicMatterCovariantDerivative (Written source current) point =
      holonomicMatterCovariantDerivative current point := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    connectionEquality,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]

private theorem written_generatedMatterVector_eq_of_connection_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (connectionEquality :
      (Written source current).gravityConnection point =
        current.gravityConnection point) :
    generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField (Written source current) point) =
      generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField current point) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    written_matterCovariantDerivative_at_eq_of_connection_eq source current
      point connectionEquality,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter]

/-- The adjoint-matter reader has the same single occurrence-local
Lorentz-connection seam as the primal reader. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatterResidual_eq_current_of_connection_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (connectionEquality :
      (Written source current).gravityConnection point =
        current.gravityConnection point) :
    (diracDualFormNativePointwiseJointResidual source
      (Written source current) point).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual source current
        point).conjugateMatter := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient source
        (Written source current) direction point =
      diracDualConjugateMatterDirectionalCoefficient source current direction
        point
  unfold diracDualConjugateMatterDirectionalCoefficient
    generatedVolumeDensity
  change
    |Matrix.det ((Written source current).coframe point)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector source 0 point
            (toContinuumPointField (Written source current) point))).re =
      |Matrix.det (current.coframe point)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector source 0 point
            (toContinuumPointField current point))).re
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    written_generatedMatterVector_eq_of_connection_eq source current point
      connectionEquality]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECFullCauchyMatterScalarReadTransport
