import H0mework.Physics.Matter.ConjugateMatterActionTimeVelocity
import H0mework.Physics.Matter.ConjugateMatterVariation
import H0mework.Physics.Geometry.DynamicBreakingVacuum
import H0mework.Physics.Holonomic.HolonomicField

/-!
# Holonomic identity-coframe conjugate-matter action response

This module extracts the configuration-level adjoint Dirac--Yukawa temporal
response from the historical C3h197 support module.  It depends only on the
current holonomic fields and the action operators:

```text
configuration U at x
→ actual conjugate spatial jet and actual connection/Yukawa operator
→ unique identity-coframe temporal dual response.
```

The response is generated before any Euler--Lagrange residual is read.  The
involutive temporal principal symbol makes the response branch-free and
unique.  This module does not install the response in an actual and does not
claim that an arbitrary coframe profile has zero densitized-principal drift.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineHolonomicIdentityCoframeConjugateMatterActionResponse

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def holonomicConjugateMatterCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterDualCoordinates (configuration.conjugateMatter point)

theorem holonomicConjugateMatterCoordinates_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates configuration) := by
  let assemble : (MatterCoordinateIndex → ℂ) →L[ℝ]
      MatterCoordinateCarrier :=
    (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm.toContinuousLinearMap
      |>.restrictScalars ℝ
  have coordinateSmooth : ContDiff ℝ ∞ (fun point index =>
      configuration.conjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) := by
    apply contDiff_pi'
    intro index
    exact smooth.2.2.2.2.2.2.2.2 index
  have assembled := assemble.contDiff.comp coordinateSmooth
  rw [show holonomicConjugateMatterCoordinates configuration =
      fun point =>
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm
          (fun index =>
            configuration.conjugateMatter point
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))) by
    funext point
    apply PiLp.ext
    intro index
    rfl]
  exact assembled

def holonomicConjugateMatterDerivativeCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    MatterCoordinateCarrier :=
  fieldDirectionalDerivative
    (holonomicConjugateMatterCoordinates configuration) point direction

theorem holonomicConjugateMatterDerivativeCoordinates_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      holonomicConjugateMatterDerivativeCoordinates configuration point
        direction) := by
  have derivativeSmooth : ContDiff ℝ ∞
      (fderiv ℝ (holonomicConjugateMatterCoordinates configuration)) :=
    (holonomicConjugateMatterCoordinates_contDiff configuration smooth
      ).fderiv_right (m := ∞) (by simp)
  simpa [holonomicConjugateMatterDerivativeCoordinates,
    fieldDirectionalDerivative] using
    derivativeSmooth.clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        coordinateDirection direction))

def holonomicConjugateMatterDerivativeDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  matterDualOfCoordinates
    (holonomicConjugateMatterDerivativeCoordinates configuration point
      direction)

def holonomicIdentityCoframeMatterConnectionOperator
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (configuration.gravityConnection point) direction) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed (configuration.gaugeConnection point direction))

def holonomicIdentityCoframeMatterAlgebraicOperator
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        (diracMatrixMatterAction (diracGamma direction)).comp
          (holonomicIdentityCoframeMatterConnectionOperator configuration
            point direction) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))

def holonomicIdentityCoframeConjugateMatterSpatialTransport
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 3,
    (holonomicConjugateMatterDerivativeDual configuration point
      direction.succ).comp
      (identityCoframeMatterPrincipal direction.succ)

def holonomicIdentityCoframeConjugateMatterKnownDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (configuration.conjugateMatter point).comp
      (holonomicIdentityCoframeMatterAlgebraicOperator configuration point) -
    holonomicIdentityCoframeConjugateMatterSpatialTransport configuration point

/-- Temporal dual response selected by the action and the involutive temporal
principal symbol. -/
def holonomicIdentityCoframeConjugateMatterActionVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (holonomicIdentityCoframeConjugateMatterKnownDual configuration point).comp
    (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

def HolonomicIdentityCoframeConjugateMatterTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  timeDerivative.comp
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) +
      holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
        point =
    (configuration.conjugateMatter point).comp
      (holonomicIdentityCoframeMatterAlgebraicOperator configuration point)

theorem holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
      (holonomicIdentityCoframeConjugateMatterActionVelocity configuration
        point) := by
  apply LinearMap.ext
  intro matter
  simp only [holonomicIdentityCoframeConjugateMatterActionVelocity,
    holonomicIdentityCoframeConjugateMatterKnownDual,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [identityCoframeMatterPrincipal_time_involutive]
  abel

theorem holonomicIdentityCoframeConjugateMatterTimeActionLaw_unique
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstLaw :
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
        first)
    (secondLaw :
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
        second) :
    first = second := by
  have composedEqual :
      first.comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) =
        second.comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) := by
    apply LinearMap.ext
    intro matter
    have firstAt := LinearMap.congr_fun firstLaw matter
    have secondAt := LinearMap.congr_fun secondLaw matter
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at firstAt secondAt
    exact add_right_cancel (firstAt.trans secondAt.symm)
  apply LinearMap.ext
  intro matter
  calc
    first matter =
        first
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      rw [identityCoframeMatterPrincipal_time_involutive]
    _ =
        second
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      exact LinearMap.congr_fun composedEqual
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection matter)
    _ = second matter := by
      rw [identityCoframeMatterPrincipal_time_involutive]

/-- At identity coframe the adjoint Dirac equation is an evolution law, not
an additional Cauchy constraint. -/
theorem holonomicIdentityCoframeConjugateMatterTimeActionLaw_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier) :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
          candidate ↔
      candidate =
        holonomicIdentityCoframeConjugateMatterActionVelocity configuration
          point := by
  constructor
  · intro candidateLaw
    exact holonomicIdentityCoframeConjugateMatterTimeActionLaw_unique
      configuration point candidate
        (holonomicIdentityCoframeConjugateMatterActionVelocity configuration
          point)
      candidateLaw
      (holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies
        configuration point)
  · rintro rfl
    exact holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies
      configuration point

theorem holonomicIdentityCoframeConjugateMatterActionVelocity_eq_zero_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicIdentityCoframeConjugateMatterActionVelocity configuration point =
          0 ↔
      holonomicIdentityCoframeConjugateMatterKnownDual configuration point =
        0 := by
  constructor
  · intro velocityZero
    apply LinearMap.ext
    intro matter
    have atPrincipal := LinearMap.congr_fun velocityZero
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection matter)
    change
      holonomicIdentityCoframeConjugateMatterKnownDual configuration point
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
              matter)) =
        0 at atPrincipal
    rw [identityCoframeMatterPrincipal_time_involutive] at atPrincipal
    exact atPrincipal
  · rintro knownZero
    rw [holonomicIdentityCoframeConjugateMatterActionVelocity, knownZero]
    rfl

end
end SaturationMonoid.PhysicsCore.StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
