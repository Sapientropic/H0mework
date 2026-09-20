import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzMatterFirstGermReadout

/-!
# C3h207c: latest-current synchronized matter-action normal form

The C3h203 judged actual inherits its primal and adjoint first germs from the
matter Cauchy state generated after the latest current's full Einstein--Cartan
resynchronization.  This module computes the two action-time coordinates
consumed by the temporal Lorentz matter-spin derivative at internal pair `2`.

These are shallow readouts of the existing source/action producer.  No
Lorentz obstruction value, tangent certificate, correction, residual inverse,
branch choice, or equation witness is accepted as input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterActionNormalForm

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzContactReadout
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRestriction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Infinitesimal matter action of one temporal Lorentz bivector coordinate.
The direction is supplied by the Lorentz variation; the matter value is read
from the already generated actual. -/
def positiveP506MatterCurrentTemporalSpinActionVector
    (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      diracMatrixMatterAction (diracGamma direction)
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              (einsteinCartanLorentzCoordinateDirection
                canonicalLorentzianTimeDirection internalPair))
            direction)
          matter)

/-- Complex-linear operator underlying the temporal spin-action vector. -/
def positiveP506MatterCurrentTemporalSpinAction
    (internalPair : Fin 6) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      (diracMatrixMatterAction (diracGamma direction)).comp
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              (einsteinCartanLorentzCoordinateDirection
                canonicalLorentzianTimeDirection internalPair))
            direction))

@[simp] theorem positiveP506MatterCurrentTemporalSpinAction_apply
    (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    positiveP506MatterCurrentTemporalSpinAction internalPair matter =
      positiveP506MatterCurrentTemporalSpinActionVector
        internalPair matter := by
  simp [positiveP506MatterCurrentTemporalSpinAction,
    positiveP506MatterCurrentTemporalSpinActionVector]

theorem
    positiveP506MatterCurrentFullSynchronizedMatterConjugateTimeDerivative_normalForm :
    actionGeneratedConjugateMatterTimeDerivative
        positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0 =
      (-Complex.I) •
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  apply LinearMap.ext
  intro matter
  simp [actionGeneratedConjugateMatterTimeDerivative,
    actionGeneratedConjugateMatterKnownDual,
    actionGeneratedConjugateMatterSpatialTransport,
    cauchyConjugateMatterSpatialDerivative,
    cauchyConjugateMatterSpatialDerivativeCoordinate,
    actionGeneratedMatterAlgebraicOperator,
    cauchyMatterVariationConnectionOperator,
    identityCoframeMatterPrincipal,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_conjugateMatter_constant,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gravityConnection_origin,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gaugeConnection_origin_zero,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_scalar_origin_vacuum,
    canonicalLorentzianTimeDirection,
    fieldDirectionalDerivative, Fin.sum_univ_three, Fin.sum_univ_four,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  rw [show
    positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
      einsteinCartanSpinContorsionCoordinates
        positiveP506MatterCurrentEinsteinCartanSpinCoordinates by rfl,
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    einsteinCartanLorentzCoordinateDirection,
    canonicalLorentzianTimeDirection,
    einsteinCartanSpinContorsionCoordinates,
    positiveP506MatterCurrentSpinCoordinatesNormalForm,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinZeroMatterCoordinate,
    hyperchargeDegreeTwoMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  ring_nf
  norm_num [pow_succ, Complex.I_mul_I]

theorem
    positiveP506MatterCurrentTemporalSpinActionVector_two_probe :
    diracSpinZeroMatterCoordinate
        (positiveP506MatterCurrentTemporalSpinActionVector
          2 diracSpinTwoMatterProbe) =
      -(Complex.I / 2) := by
  simp [positiveP506MatterCurrentTemporalSpinActionVector,
    einsteinCartanLorentzCoordinateDirection,
    canonicalLorentzianTimeDirection,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinTwoMatterProbe,
    diracSpinZeroMatterCoordinate, hyperchargeDegreeTwoMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  ring_nf
  simp [p286HyperchargeMatterProbe]

theorem
    positiveP506MatterCurrentFullSynchronizedMatterRawVelocityTemporalSpinCoordinate_two :
    diracSpinZeroMatterCoordinate
        (positiveP506MatterCurrentTemporalSpinActionVector 2
          (actionGeneratedMatterRawTimeVelocity
            positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0)) =
      (1 / 2 : ℂ) := by
  simp [positiveP506MatterCurrentTemporalSpinActionVector,
    actionGeneratedMatterRawTimeVelocity,
    actionGeneratedMatterTimeCovariantDerivative,
    actionGeneratedMatterKnownVector,
    cauchyMatterSpatialCovariantDerivative,
    cauchyMatterSpatialDerivativeCoordinate,
    cauchyMatterConnectionAction,
    identityCoframeMatterTimePrincipal,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_constant,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gravityConnection_origin,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gaugeConnection_origin_zero,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_scalar_origin_vacuum,
    fieldDirectionalDerivative, Fin.sum_univ_three, Fin.sum_univ_four,
    chiralExteriorYukawaAction_degreeTwo_eq_zero,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  rw [show
    positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
      einsteinCartanSpinContorsionCoordinates
        positiveP506MatterCurrentEinsteinCartanSpinCoordinates by rfl,
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    einsteinCartanLorentzCoordinateDirection,
    canonicalLorentzianTimeDirection,
    einsteinCartanSpinContorsionCoordinates,
    positiveP506MatterCurrentSpinCoordinatesNormalForm,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinTwoMatterProbe,
    diracSpinZeroMatterCoordinate, hyperchargeDegreeTwoMatterCoordinate,
    hyperchargeDegreeTwoMatterCoordinate_probe,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  ring_nf
  rw [chiralExteriorYukawaAction_degreeTwo_eq_zero]
  simp [p286HyperchargeMatterProbe,
    hyperchargeDegreeTwoMatterCoordinate_probe]
  norm_num [pow_succ, Complex.I_mul_I]

theorem
    positiveP506MatterCurrentFullSynchronizedMatterSpinTimeReadout_two_eq_zero :
    ((actionGeneratedConjugateMatterTimeDerivative
          positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0)
          (positiveP506MatterCurrentTemporalSpinActionVector 2
            (positiveP506MatterCurrentFullSynchronizedMatterCauchyState.matter
              0)) +
        (positiveP506MatterCurrentFullSynchronizedMatterCauchyState.conjugateMatter
          0)
          (positiveP506MatterCurrentTemporalSpinActionVector 2
            (actionGeneratedMatterRawTimeVelocity
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0))).re =
      0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedMatterConjugateTimeDerivative_normalForm,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_origin,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_conjugateMatter_origin]
  change
    ((-Complex.I) *
          diracSpinZeroMatterCoordinate
            (positiveP506MatterCurrentTemporalSpinActionVector
              2 diracSpinTwoMatterProbe) +
        diracSpinZeroMatterCoordinate
          (positiveP506MatterCurrentTemporalSpinActionVector 2
            (actionGeneratedMatterRawTimeVelocity
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0))).re =
      0
  rw [positiveP506MatterCurrentTemporalSpinActionVector_two_probe,
    positiveP506MatterCurrentFullSynchronizedMatterRawVelocityTemporalSpinCoordinate_two]
  norm_num [Complex.I_mul_I]

/-- The source/action-generated primal and adjoint time velocities cancel in
the matter-spin Lorentz readout for every internal bivector coordinate.  This
is an actual normal-form computation, not a supplied Lorentz constraint. -/
theorem
    positiveP506MatterCurrentFullSynchronizedMatterSpinTimeReadout_eq_zero
    (internalPair : Fin 6) :
    ((actionGeneratedConjugateMatterTimeDerivative
          positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0)
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (positiveP506MatterCurrentFullSynchronizedMatterCauchyState.matter
              0)) +
        (positiveP506MatterCurrentFullSynchronizedMatterCauchyState.conjugateMatter
          0)
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (actionGeneratedMatterRawTimeVelocity
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0))).re =
      0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedMatterConjugateTimeDerivative_normalForm,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_origin,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_conjugateMatter_origin]
  change
    ((-Complex.I) *
          diracSpinZeroMatterCoordinate
            (positiveP506MatterCurrentTemporalSpinActionVector
              internalPair diracSpinTwoMatterProbe) +
        diracSpinZeroMatterCoordinate
          (positiveP506MatterCurrentTemporalSpinActionVector internalPair
            (actionGeneratedMatterRawTimeVelocity
              positiveP506MatterCurrentFullSynchronizedMatterCauchyState
              0))).re =
      0
  fin_cases internalPair <;>
    simp [positiveP506MatterCurrentTemporalSpinActionVector,
      actionGeneratedMatterRawTimeVelocity,
      actionGeneratedMatterTimeCovariantDerivative,
      actionGeneratedMatterKnownVector,
      cauchyMatterSpatialCovariantDerivative,
      cauchyMatterSpatialDerivativeCoordinate,
      cauchyMatterConnectionAction,
      identityCoframeMatterTimePrincipal,
      positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_constant,
      positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gravityConnection_origin,
      positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gaugeConnection_origin_zero,
      positiveP506MatterCurrentFullSynchronizedMatterCauchyState_scalar_origin_vacuum,
      fieldDirectionalDerivative, Fin.sum_univ_three, Fin.sum_univ_four,
      chiralExteriorYukawaAction_degreeTwo_eq_zero,
      diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  all_goals
    rw [show
      positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
        einsteinCartanSpinContorsionCoordinates
          positiveP506MatterCurrentEinsteinCartanSpinCoordinates by rfl,
      positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
    simp [lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      einsteinCartanLorentzCoordinateDirection,
      canonicalLorentzianTimeDirection,
      einsteinCartanSpinContorsionCoordinates,
      positiveP506MatterCurrentSpinCoordinatesNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate, hyperchargeDegreeTwoMatterCoordinate,
      hyperchargeDegreeTwoMatterCoordinate_probe,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
    ring_nf
    try simp [p286HyperchargeMatterProbe,
      hyperchargeDegreeTwoMatterCoordinate_probe,
      pow_succ, Complex.I_mul_I]
  all_goals
    rw [chiralExteriorYukawaAction_degreeTwo_eq_zero]
    simp [p286HyperchargeMatterProbe,
      hyperchargeDegreeTwoMatterCoordinate_probe,
      pow_succ, Complex.I_mul_I]

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterActionNormalForm
