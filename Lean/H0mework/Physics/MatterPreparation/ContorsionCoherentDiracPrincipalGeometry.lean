import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileDiracPrincipalGeometry
import H0mework.Physics.MatterPreparation.ContorsionCoherentBFMomentumRegularity

/-!
# S9-C3h201d: final coherent Dirac-principal geometry

The C3h200r final coherent actual pulls the generated P506 spatial coframe
through the canonical zero-slice projection.  On each matching coordinate
axis this pullback is exactly the original generated profile:

```text
final coherent actual
→ exact four-axis coframe path
→ exact inverse-gamma principal
→ zero density derivative
→ zero densitized Dirac-principal drift.
```

This is a positive operator transport on the final actual.  It controls only
the geometric principal with a fixed matter input.  It does not replace the
independent proof that the final actual carries the generated primal and dual
field germs.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentDiracPrincipalGeometry

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineDynamicBreakingVacuum
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileDiracPrincipalGeometry
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentBFMomentumRegularity

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The zero-slice pullback preserves all three spatial axes.  On the time
axis both the pullback and the generated spatial profile are the identity
coframe because the source/action-generated temporal jet row is zero. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_axis
    (direction : LorentzianIndex) (parameter : ℝ) :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
        (parameter • coordinateDirection direction) =
      preContorsionSpatialProfileActual.coframe
        (parameter • coordinateDirection direction) := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_normalForm]
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · rw [ContinuousLinearMap.map_smul]
    change
      preContorsionSpatialProfileActual.coframe
          (parameter •
            canonicalZeroSliceProjection
              (coordinateDirection canonicalLorentzianTimeDirection)) =
        preContorsionSpatialProfileActual.coframe
          (parameter • coordinateDirection canonicalLorentzianTimeDirection)
    rw [canonicalZeroSliceProjection_coordinateTime, smul_zero,
      preContorsionSpatialProfileActual_coframe_axis]
    rw [preContorsionSpatialProfileActual_coframe_origin]
    rw [spatialSkewCoframeJetLift_time]
    ext internal coordinate
    simp [skewCoframeAxis,
      StageNineLorentzConnectionVariation.loweredLorentzBivectorMatrix]
  · rw [ContinuousLinearMap.map_smul,
      canonicalZeroSliceProjection_coordinateSpatial]

/-- The final coherent actual has the same inverse Dirac gamma on every
matching coordinate axis as the generated profile. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_inverseGamma_axis
    (direction : LorentzianIndex) (parameter : ℝ) :
    inverseCoframeDiracGamma
        { coframe :=
            positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
              (parameter • coordinateDirection direction)
          derivative := 0 }
        direction =
      diracGamma direction := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_axis]
  exact preContorsionSpatialProfileActual_inverseGamma_axis direction parameter

/-- Final-actual version of the matching-axis densitized matter principal. -/
def
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalAxis
    (direction : LorentzianIndex)
    (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    MatterCoordinateCarrier :=
  matterCoordinateEquiv
    (abs
        (Matrix.det
          (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
            (parameter • coordinateDirection direction))) •
      (Complex.I •
        diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe :=
                positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
                  (parameter • coordinateDirection direction)
              derivative := 0 }
            direction)
          matter))

theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalAxis_eq_profile
    (direction : LorentzianIndex)
    (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalAxis
        direction parameter matter =
      preContorsionSpatialProfileActualDensitizedMatterPrincipalAxis
        direction parameter matter := by
  unfold
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalAxis
    preContorsionSpatialProfileActualDensitizedMatterPrincipalAxis
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_axis]

/-- Every coordinate contribution has zero first derivative on the actual
final coherent carrier. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_densitizedMatterPrincipal_axis_hasDerivAt_zero
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    HasDerivAt
      (fun parameter : ℝ =>
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalAxis
          direction parameter matter)
      0 0 := by
  simpa only [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalAxis_eq_profile]
    using
      preContorsionSpatialProfileActual_densitizedMatterPrincipal_axis_hasDerivAt_zero
        direction matter

/-- Complete fixed-input geometric principal divergence on the final actual. -/
def
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalDivergenceOrigin
    (matter : DiracExteriorMatterCarrier) :
    MatterCoordinateCarrier :=
  ∑ direction : LorentzianIndex,
    deriv
      (fun parameter : ℝ =>
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalAxis
          direction parameter matter)
      0

theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_densitizedMatterPrincipalDivergence_origin :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalDivergenceOrigin =
      0 := by
  funext matter
  unfold
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActualDensitizedMatterPrincipalDivergenceOrigin
  apply Finset.sum_eq_zero
  intro direction _
  exact
    (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_densitizedMatterPrincipal_axis_hasDerivAt_zero
      direction matter).deriv

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentDiracPrincipalGeometry
