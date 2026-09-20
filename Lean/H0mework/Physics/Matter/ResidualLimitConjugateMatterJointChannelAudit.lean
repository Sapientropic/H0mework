import H0mework.Physics.Lorentz.ResidualLimitLorentzTransportJointChannelAudit

/-!
# S9-C3h37: conjugate-matter closure on the C3h33 readers

The C3h33 reference and endpoint readers have primitive matter identically
zero.  This audit expands the actual holonomic covariant derivative and the
actual Dirac--Yukawa vector.  Coordinate derivative, Lorentz-spin action,
P286 action, Dirac kinetic sum, and Yukawa action all vanish on that primitive
zero field.  The resulting actual conjugate-matter Euler--Lagrange coordinate
is zero on both readers and therefore obeys `r' = (1 - sigma) r`.

No matter-orbit realizer, equation receipt, zero-fiber witness, stationarity
premise, or target residual is accepted.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitConjugateMatterJointChannelAudit

open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzTransportJointChannelAudit
open SU7ExteriorBreakingYukawa

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 200000

/-! ## Primitive zero matter forces the actual covariant derivative to zero -/

/-- This expands all three terms in the holonomic derivative.  In particular,
the primitive Lorentz and P286 connections are not assumed to vanish; their
linear actions vanish because the acted-on matter field is zero. -/
theorem holonomicMatterCovariantDerivative_zero_of_matter_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (matterZero : configuration.matter = 0) :
    holonomicMatterCovariantDerivative configuration 0 = 0 := by
  funext direction
  have coordinateDerivativeZero :
      fieldDirectionalDerivative
          (fun candidate =>
            matterCoordinateEquiv (configuration.matter candidate))
          0 direction = 0 := by
    rw [matterZero]
    change fieldDirectionalDerivative
      (fun _ : BasePoint => matterCoordinateEquiv 0) 0 direction = 0
    simp [fieldDirectionalDerivative]
  have matterOriginZero : configuration.matter 0 = 0 := by
    rw [matterZero]
    rfl
  unfold holonomicMatterCovariantDerivative
  rw [coordinateDerivativeZero, matterOriginZero]
  simp

theorem jointAuditReference_matterCovariantDerivative_origin_zero :
    holonomicMatterCovariantDerivative residualLimitLorentzCarrierReader 0 = 0 :=
  holonomicMatterCovariantDerivative_zero_of_matter_eq_zero
    residualLimitLorentzCarrierReader (by rfl)

/-- The endpoint result uses C3h33's actual derived-jet equality, then the
independent reference zero calculation above. -/
theorem jointAuditEndpoint_matterCovariantDerivative_origin_zero :
    holonomicMatterCovariantDerivative jointAuditEndpointReader 0 = 0 :=
  jointAuditEndpointReader_matterCovariantDerivative_origin.trans
    jointAuditReference_matterCovariantDerivative_origin_zero

/-! ## Actual Dirac--Yukawa vector -/

/-- Expanding the real vector shows exactly why zero matter alone is not used
as a slogan: both its generated covariant derivative and the Yukawa input are
explicitly required to vanish. -/
theorem generatedContinuumMatterVector_zero_of_matter_and_derivative_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (matterOriginZero : configuration.matter 0 = 0)
    (derivativeZero :
      holonomicMatterCovariantDerivative configuration 0 = 0) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField configuration 0) = 0 := by
  unfold generatedContinuumMatterVector
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart, matterFrameRelative_zeroChart]
  rw [derivativeZero, matterOriginZero]
  simp [chiralExteriorYukawaAction]

theorem jointAuditReference_generatedContinuumMatterVector_origin_zero :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField residualLimitLorentzCarrierReader 0) = 0 :=
  generatedContinuumMatterVector_zero_of_matter_and_derivative_zero
    positiveSmoothUnifiedSource residualLimitLorentzCarrierReader (by rfl)
      jointAuditReference_matterCovariantDerivative_origin_zero

theorem jointAuditEndpoint_generatedContinuumMatterVector_origin_zero :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField jointAuditEndpointReader 0) = 0 :=
  generatedContinuumMatterVector_zero_of_matter_and_derivative_zero
    positiveSmoothUnifiedSource jointAuditEndpointReader (by rfl)
      jointAuditEndpoint_matterCovariantDerivative_origin_zero

/-! ## Actual conjugate-matter EL residual and transport -/

theorem conjugateMatterDirectionalCoefficient_zero_of_vector_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (vectorZero :
      generatedContinuumMatterVector source 0 0
        (toContinuumPointField configuration 0) = 0) :
    (fun direction =>
      conjugateMatterDirectionalCoefficient source configuration direction 0) =
        0 := by
  funext direction
  unfold conjugateMatterDirectionalCoefficient
  rw [vectorZero]
  simp

theorem jointAuditReference_conjugateMatterResidual_zero :
    jointAuditReferenceResidual.eulerLagrange.conjugateMatter = 0 := by
  change (fun direction =>
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
      residualLimitLorentzCarrierReader direction 0) = 0
  exact conjugateMatterDirectionalCoefficient_zero_of_vector_zero
    positiveSmoothUnifiedSource residualLimitLorentzCarrierReader
      jointAuditReference_generatedContinuumMatterVector_origin_zero

theorem jointAuditEndpoint_conjugateMatterResidual_zero :
    jointAuditEndpointResidual.eulerLagrange.conjugateMatter = 0 := by
  change (fun direction =>
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
      jointAuditEndpointReader direction 0) = 0
  exact conjugateMatterDirectionalCoefficient_zero_of_vector_zero
    positiveSmoothUnifiedSource jointAuditEndpointReader
      jointAuditEndpoint_generatedContinuumMatterVector_origin_zero

/-- Actual C3h33 conjugate-matter transport.  Both sides are computed zeros;
the proof does not infer transport merely from endpoint/reference equality. -/
theorem jointAuditEndpoint_conjugateMatterResidual_transport :
    jointAuditEndpointResidual.eulerLagrange.conjugateMatter =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        jointAuditReferenceResidual.eulerLagrange.conjugateMatter := by
  rw [jointAuditEndpoint_conjugateMatterResidual_zero,
    jointAuditReference_conjugateMatterResidual_zero, smul_zero]

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitConjugateMatterJointChannelAudit
