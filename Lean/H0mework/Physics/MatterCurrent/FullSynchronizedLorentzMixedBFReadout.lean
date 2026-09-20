import H0mework.Physics.SynchronizedJoint.MixedBFReadout
import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzFirstVariationObstruction

/-!
# C3h205: latest-current Lorentz mixed-BF calculation

This module specializes the generic time-affine BF-momentum normal form to
the exact P506/L0 C3h203 actual.  The three spatial derivatives vanish on
that same actual, so its temporal-Gauss first variation reduces from

```text
gravity-BF + matter-spin + mixed-BF
```

to `gravity-BF + matter-spin`.

The temporal BF response itself is retained and may be nonzero.  No old
C3h202 first jet, obstruction value, response target, correction, branch,
or stationarity certificate is transported into the calculation.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMixedBFReadout

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineCurrentFullSynchronizedLorentzMixedBFReadout
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionVariation
open StageNineLorentzTemporalGaussFirstVariation
open StageNineLorentzTemporalGaussResidualTangency
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzFirstVariationObstruction
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private abbrev CurrentState : StageNineCauchyState :=
  PreContorsionFullLorentzTriangularCurrent

private abbrev JudgedActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentFullSynchronizedLorentzActual

/-! ## Same-actual mixed-BF calculation -/

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_spatialBFMomentumDivergence_zero
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionSpatialBFMomentumDivergence JudgedActual direction point =
      0 := by
  exact
    currentFullSynchronizedLorentzActualFirstJetLift_spatialBFMomentumDivergence_zero
      positiveSmoothUnifiedSource CurrentState 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin direction point

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMixedBFTangencyTerm_eq_zero
    (component : LorentzTemporalBivectorDirection) :
    positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.mixedBF
        component =
      0 := by
  exact
    currentFullSynchronizedLorentzActualFirstJetLift_mixedBFTangencyTerm_zero
      positiveSmoothUnifiedSource CurrentState 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin component

/-- The actual obstruction now has a two-sector normal form.  This does not
set either surviving sector, or their sum, to zero. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_gravityBF_add_matterSpin
    (component : LorentzTemporalBivectorDirection) :
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
        component =
      positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.gravityBF
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.matterSpin
          component := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_sectors,
    positiveP506MatterCurrentFullSynchronizedLorentzMixedBFTangencyTerm_eq_zero]
  ring

/-- Genuine derivative provenance for the reduced two-sector coefficient on
the identical temporal-Gauss trace. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_lorentzTemporalGaussResidual_timeTrace_hasDerivAt_gravityBF_add_matterSpin
    (component : LorentzTemporalBivectorDirection) :
    HasDerivAt
      (lorentzTemporalGaussResidualTimeTrace positiveSmoothUnifiedSource
        JudgedActual 0 component)
      (positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.gravityBF
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.matterSpin
          component)
      0 := by
  exact
    (positiveP506MatterCurrentFullSynchronizedLorentzActual_lorentzTemporalGaussResidual_timeTrace_hasDerivAt_obstruction
      component).congr_deriv
        (positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_gravityBF_add_matterSpin
          component)

/-! ## No-premise exact-source checkpoint -/

structure
    PositiveP506MatterCurrentFullSynchronizedLorentzMixedBFReadoutLaw :
    Prop where
  positiveC3h204 :
    PositiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannelsLaw
  spatialDivergenceZero : ∀ direction point,
    lorentzConnectionSpatialBFMomentumDivergence JudgedActual direction point =
      0
  mixedBFTangencyZero : ∀ component,
    positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.mixedBF
        component =
      0
  reducedObstruction : ∀ component,
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
        component =
      positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.gravityBF
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.matterSpin
          component
  reducedFirstVariation : ∀ component,
    HasDerivAt
      (lorentzTemporalGaussResidualTimeTrace positiveSmoothUnifiedSource
        JudgedActual 0 component)
      (positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.gravityBF
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.matterSpin
          component)
      0

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzMixedBFReadout_realizes_C3h205 :
    PositiveP506MatterCurrentFullSynchronizedLorentzMixedBFReadoutLaw := by
  exact
    { positiveC3h204 :=
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels_realizes_C3h204
      spatialDivergenceZero :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_spatialBFMomentumDivergence_zero
      mixedBFTangencyZero :=
        positiveP506MatterCurrentFullSynchronizedLorentzMixedBFTangencyTerm_eq_zero
      reducedObstruction :=
        positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_gravityBF_add_matterSpin
      reducedFirstVariation :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_lorentzTemporalGaussResidual_timeTrace_hasDerivAt_gravityBF_add_matterSpin }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMixedBFReadout
