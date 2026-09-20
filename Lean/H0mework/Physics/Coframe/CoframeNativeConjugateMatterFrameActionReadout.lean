import H0mework.Physics.Coframe.CoframeNativeConjugateMatterFrameAction

namespace SaturationMonoid.PhysicsCore

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineCoframeNativeMatterFrameAction
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false

local instance coframeNativeReadoutMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private theorem matterDualOfCoordinates_sum
    {indexType : Type} [Fintype indexType]
    (coordinates : indexType → MatterCoordinateCarrier) :
    matterDualOfCoordinates (∑ index, coordinates index) =
      ∑ index, matterDualOfCoordinates (coordinates index) := by
  classical
  induction (Finset.univ : Finset indexType) using Finset.induction_on with
  | empty => simp
  | @insert index indices indexNotMem inductionHypothesis =>
      rw [Finset.sum_insert indexNotMem, Finset.sum_insert indexNotMem,
        StageNineIdentityCoframeConjugateMatterTimeResponseActualLift.matterDualOfCoordinates_add,
        inductionHypothesis]

/-- The frame-basis adjoint law is the complete coordinate-basis live law
transported through the current coframe. -/
theorem frameTimeActionLaw_iff_liveCoframeTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
        configuration point
        (holonomicFrameConjugateMatterDerivative configuration point 0) ↔
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
        configuration point
        (holonomicConjugateMatterDerivativeDual configuration point 0) := by
  have transportEq := conjugateMatterPrincipalTransport_eq_frame
    (configuration.coframe point)
    (holonomicConjugateMatterDerivativeDual configuration point)
  have scaledTransportEq := congrArg
    (fun transport : Module.Dual ℂ DiracExteriorMatterCarrier =>
      (generatedVolumeDensity
        (toContinuumPointField configuration point) : ℂ) • transport)
    transportEq
  have liveTimeEq :
      liveCoframeMatterPrincipal (configuration.coframe point) 0 =
        currentCoframeMatterTemporalPrincipal
          (configuration.coframe point) :=
    rfl
  unfold HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    holonomicFrameConjugateMatterDerivative
    holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
    holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
  simp_rw [matterDualOfCoordinates_sum, matterDualOfCoordinates_surjective]
  simp [Fin.sum_univ_four, Fin.sum_univ_three,
    holonomicFrameConjugateMatterDerivative,
    canonicalLorentzianTimeDirection] at scaledTransportEq ⊢
  rw [liveTimeEq] at scaledTransportEq
  let density : ℂ :=
    generatedVolumeDensity (toContinuumPointField configuration point)
  let coordinateTime : Module.Dual ℂ DiracExteriorMatterCarrier :=
    density •
      (holonomicConjugateMatterDerivativeDual configuration point 0).comp
        (currentCoframeMatterTemporalPrincipal (configuration.coframe point))
  let coordinateSpatial : Module.Dual ℂ DiracExteriorMatterCarrier :=
    density •
        (holonomicConjugateMatterDerivativeDual configuration point 1).comp
          (liveCoframeMatterPrincipal (configuration.coframe point) 1) +
      density •
        (holonomicConjugateMatterDerivativeDual configuration point 2).comp
          (liveCoframeMatterPrincipal (configuration.coframe point) 2) +
      density •
        (holonomicConjugateMatterDerivativeDual configuration point 3).comp
          (liveCoframeMatterPrincipal (configuration.coframe point) 3)
  let frameTime : Module.Dual ℂ DiracExteriorMatterCarrier :=
    density •
      (frameConjugateMatterDerivative (configuration.coframe point)
          (holonomicConjugateMatterDerivativeDual configuration point) 0).comp
        (identityCoframeMatterPrincipal 0)
  let frameSpatial : Module.Dual ℂ DiracExteriorMatterCarrier :=
    density •
        (frameConjugateMatterDerivative (configuration.coframe point)
            (holonomicConjugateMatterDerivativeDual configuration point) 1).comp
          (identityCoframeMatterPrincipal 1) +
      density •
        (frameConjugateMatterDerivative (configuration.coframe point)
            (holonomicConjugateMatterDerivativeDual configuration point) 2).comp
          (identityCoframeMatterPrincipal 2) +
      density •
        (frameConjugateMatterDerivative (configuration.coframe point)
            (holonomicConjugateMatterDerivativeDual configuration point) 3).comp
          (identityCoframeMatterPrincipal 3)
  let algebraic : Module.Dual ℂ DiracExteriorMatterCarrier :=
    holonomicDiracDualLiveCoframeAlgebraicDual configuration point
  let spatialDrift : Module.Dual ℂ DiracExteriorMatterCarrier :=
    matterDualOfCoordinates
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates configuration point)
  let temporalDrift : Module.Dual ℂ DiracExteriorMatterCarrier :=
    matterDualOfCoordinates
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates configuration point)
  change
    frameTime = algebraic - frameSpatial - (spatialDrift + temporalDrift) ↔
      coordinateTime =
        algebraic - coordinateSpatial - spatialDrift - temporalDrift
  have transportTotals :
      coordinateTime + coordinateSpatial = frameTime + frameSpatial := by
    dsimp [coordinateTime, coordinateSpatial, frameTime, frameSpatial, density]
    simpa only [add_assoc] using scaledTransportEq
  constructor
  · intro frameLaw
    have frameTotal :
        frameTime + frameSpatial = algebraic - spatialDrift - temporalDrift := by
      rw [frameLaw]
      abel
    have coordinateTotal :
        coordinateTime + coordinateSpatial =
          algebraic - spatialDrift - temporalDrift := by
      rw [transportTotals, frameTotal]
    calc
      coordinateTime =
          (coordinateTime + coordinateSpatial) - coordinateSpatial := by
            abel
      _ = (algebraic - spatialDrift - temporalDrift) - coordinateSpatial := by
            rw [coordinateTotal]
      _ = algebraic - coordinateSpatial - spatialDrift - temporalDrift := by
            abel
  · intro coordinateLaw
    have coordinateTotal :
        coordinateTime + coordinateSpatial =
          algebraic - spatialDrift - temporalDrift := by
      rw [coordinateLaw]
      abel
    have frameTotal :
        frameTime + frameSpatial = algebraic - spatialDrift - temporalDrift := by
      rw [← transportTotals]
      exact coordinateTotal
    calc
      frameTime = (frameTime + frameSpatial) - frameSpatial := by
        abel
      _ = (algebraic - spatialDrift - temporalDrift) - frameSpatial := by
        rw [frameTotal]
      _ = algebraic - frameSpatial - (spatialDrift + temporalDrift) := by
        abel

end
end SaturationMonoid.PhysicsCore
