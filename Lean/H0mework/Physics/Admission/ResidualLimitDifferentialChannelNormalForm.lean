import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.GravitySource.ResidualOrbitConnectionLift
import H0mework.Physics.MatterJets.SourceMatterFirstJetResidualOrbit

/-!
# S9-C3h21: residual-limit differential-channel normal forms

This module returns from the C3h20 required-response carrier to actual
configuration residuals.  A C3h15 matter-orbit realizer has zero matter value
at the origin.  Therefore its Lorentz matter-spin current and P286 matter
current vanish.  In the residual-limit six-field class, the scalar is at the
source-generated vacuum, so the scalar potential variation also vanishes;
the zero matter value kills its Yukawa variation.

The resulting exact origin normal forms are deliberately not closures:

* Lorentz leaves the gravity-BF balance;
* P286 leaves gauge-BF balance plus scalar current;
* scalar leaves kinetic algebraic response minus differential divergence.

No theorem here says those remaining responses vanish or are realized by a
source-generated higher jet.  Matter and coframe remain entirely open.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitDifferentialChannelNormalForm

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageEightSourceGeneratedMatter
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineConjugateMatterVariation
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceMatterFirstJetResidualOrbit
open StageNineConnectionSectorSourceBalance
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open DiracExteriorMatterAction
open SU7ExteriorBreakingYukawa

noncomputable section

set_option autoImplicit false

theorem realizingOrbit_matter_origin_eq_zero
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration) :
    configuration.matter 0 = 0 := by
  simpa [sourceGeneratedMatterJet] using realizes.matterOrigin

theorem realizingOrbit_lorentzMatterSpinSource_origin_eq_zero
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration)
    (direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        configuration direction 0 = 0 := by
  unfold lorentzMatterSpinSourceCoefficient
  unfold holonomicMatterLorentzConnectionVariation
  rw [show configuration.matter 0 = 0 from
    realizingOrbit_matter_origin_eq_zero n configuration realizes]
  simp [matterGaugeConnectionFirstVariationDensity,
    matterGaugeConnectionVariationVector, matterGaugeKineticSum]

/-- Under the required matter-orbit realization, the Lorentz channel has
exactly the gravity-BF balance left. -/
theorem realizingOrbit_lorentzResidual_origin_eq_gravityBFBalance
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration)
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        configuration direction 0 =
      lorentzGravityBFBalanceCoefficient configuration direction 0 := by
  rw [lorentzConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    realizingOrbit_lorentzMatterSpinSource_origin_eq_zero
      n configuration realizes]
  ring

theorem realizingOrbit_p286MatterCurrent_origin_eq_zero
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration)
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource configuration
        direction 0 = 0 := by
  unfold p286MatterCurrentCoefficient
  unfold holonomicMatterGaugeConnectionVariation
  rw [show configuration.matter 0 = 0 from
    realizingOrbit_matter_origin_eq_zero n configuration realizes]
  simp [matterGaugeConnectionFirstVariationDensity,
    matterGaugeConnectionVariationVector, matterGaugeKineticSum]

/-- The P286 channel reduces to its gauge-BF balance plus the actual scalar
current.  Neither remaining term is discarded. -/
theorem realizingOrbit_p286Residual_origin_eq_bfBalance_add_scalarCurrent
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        configuration direction 0 =
      p286GaugeBFBalanceCoefficient configuration direction 0 +
        p286ScalarCurrentCoefficient positiveSmoothUnifiedSource configuration
          direction 0 := by
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    realizingOrbit_p286MatterCurrent_origin_eq_zero
      n configuration realizes]
  ring

theorem realizingOrbit_scalarYukawa_origin_eq_zero
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration)
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField configuration 0) direction = 0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  change
    (configuration.conjugateMatter 0
      (chiralExteriorYukawaAction
        (scalarCoordinateEquiv.symm direction) (configuration.matter 0))).re = 0
  rw [show configuration.matter 0 = 0 from
    realizingOrbit_matter_origin_eq_zero n configuration realizes]
  simp [chiralExteriorYukawaAction]

theorem residualLimitExtension_scalarPotential_origin_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration)
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField configuration 0) direction = 0 := by
  have scalarOrigin :
      configuration.scalar 0 =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    rw [extension.scalar]
    change generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
    unfold generatedLocalVacuumCoordinates generatedScalarFrame
    rw [generatedTransition_normalized]
    exact scalarCoordinateAction_one _
  unfold scalarPotentialFirstVariation
  change frameRelativeScalarGradient
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
      (configuration.scalar 0) direction = 0
  rw [scalarOrigin]
  exact congrFun
    (frameRelativeScalarGradient_at_target
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)) direction

/-- At the residual-limit mouth plus matter-orbit realization, the scalar
channel has only the kinetic algebraic response and its actual differential
momentum divergence left. -/
theorem residualLimitRealizingOrbit_scalarResidual_origin_eq_kineticBalance
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration)
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        configuration direction 0 =
      generatedVolumeDensity (toContinuumPointField configuration 0) *
          scalarGaugeConnectionKineticFirstVariationDensity
            positiveSmoothUnifiedSource 0 0
            (toContinuumPointField configuration 0)
            (holonomicScalarVariationAlgebraicDirection configuration
              direction 0) -
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          configuration direction 0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
    scalarAlgebraicDirectionalCoefficient
  rw [residualLimitExtension_scalarPotential_origin_eq_zero
      configuration extension direction,
    realizingOrbit_scalarYukawa_origin_eq_zero
      n configuration realizes direction]
  ring

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitDifferentialChannelNormalForm
