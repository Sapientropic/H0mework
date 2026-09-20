import H0mework.Physics.Coframe.CoframeNativeMatterFrameAction
import H0mework.Physics.CoframeResponse.MatterActionResponse

/-!
# Coframe-native conjugate-matter frame action

This module rewrites the complete live-coframe adjoint principal transport in
the coframe-generated frame basis.  The density/inverse-coframe drift remains
an explicit action term; changing basis does not discard it.

The resulting frame-time law and its unique solution consume only the current
coframe, conjugate-matter first jet, and the already generated live-coframe
action terms.  They do not install a field or read an Euler residual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeConjugateMatterFrameAction

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeMatterFrameAction
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterPointwiseEquation
open StageNineP286ActionCauchySplit
open scoped Matrix

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

local instance coframeNativeAdjointMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

abbrev ConjugateMatterDerivativeFamily :=
  LorentzianIndex → Module.Dual ℂ DiracExteriorMatterCarrier

/-- Coordinate derivatives of the adjoint field read in the inverse-frame
basis. -/
def frameConjugateMatterDerivative
    (coframe : LorentzianCoframe)
    (coordinateDerivative : ConjugateMatterDerivativeFamily)
    (internal : LorentzianIndex) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  ∑ coordinate : LorentzianIndex,
    (coframe⁻¹ coordinate internal : ℂ) • coordinateDerivative coordinate

/-- Frame derivatives reconstructed in the coordinate basis. -/
def coordinateConjugateMatterDerivative
    (coframe : LorentzianCoframe)
    (frameDerivative : ConjugateMatterDerivativeFamily)
    (coordinate : LorentzianIndex) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  ∑ internal : LorentzianIndex,
    (coframe internal coordinate : ℂ) • frameDerivative internal

theorem coordinateConjugateMatterDerivative_frameConjugateMatterDerivative
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coordinateDerivative : ConjugateMatterDerivativeFamily) :
    coordinateConjugateMatterDerivative coframe
        (frameConjugateMatterDerivative coframe coordinateDerivative) =
      coordinateDerivative := by
  funext coordinate
  unfold coordinateConjugateMatterDerivative frameConjugateMatterDerivative
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,
    show ∀ sourceCoordinate,
      (∑ internal : LorentzianIndex,
        (coframe internal coordinate : ℂ) *
          (coframe⁻¹ sourceCoordinate internal : ℂ)) =
        ((1 : LorentzianCoframe) sourceCoordinate coordinate : ℂ) by
      intro sourceCoordinate
      simpa [mul_comm] using inverse_mul_coframe_complex coframe
        nondegenerate sourceCoordinate coordinate]
  rw [Finset.sum_eq_single coordinate]
  · simp
  · intro candidate _ candidateNe
    simp [candidateNe]
  · simp

theorem frameConjugateMatterDerivative_coordinateConjugateMatterDerivative
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (frameDerivative : ConjugateMatterDerivativeFamily) :
    frameConjugateMatterDerivative coframe
        (coordinateConjugateMatterDerivative coframe frameDerivative) =
      frameDerivative := by
  funext internal
  unfold coordinateConjugateMatterDerivative frameConjugateMatterDerivative
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,
    show ∀ sourceInternal,
      (∑ coordinate : LorentzianIndex,
        (coframe⁻¹ coordinate internal : ℂ) *
          (coframe sourceInternal coordinate : ℂ)) =
        ((1 : LorentzianCoframe) sourceInternal internal : ℂ) by
      intro sourceInternal
      simpa [mul_comm] using coframe_mul_inverse_complex coframe
        nondegenerate sourceInternal internal]
  rw [Finset.sum_eq_single internal]
  · simp
  · intro candidate _ candidateNe
    simp [candidateNe]
  · simp

/-- Each coordinate principal is the inverse-coframe combination of the
fixed internal-frame principals. -/
theorem liveCoframeMatterPrincipal_eq_frame_sum
    (coframe : LorentzianCoframe)
    (coordinate : LorentzianIndex) :
    liveCoframeMatterPrincipal coframe coordinate =
      ∑ internal : LorentzianIndex,
        (coframe⁻¹ coordinate internal : ℂ) •
          identityCoframeMatterPrincipal internal := by
  apply LinearMap.ext
  intro matter
  unfold liveCoframeMatterPrincipal identityCoframeMatterPrincipal
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [diracMatrixMatterAction_inverseGamma_expand]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro internal _
  rw [smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

/-- The complete coordinate principal transport equals the complete frame
principal transport.  This is a basis change, not an equation of motion. -/
theorem conjugateMatterPrincipalTransport_eq_frame
    (coframe : LorentzianCoframe)
    (coordinateDerivative : ConjugateMatterDerivativeFamily) :
    (∑ coordinate : LorentzianIndex,
        (coordinateDerivative coordinate).comp
          (liveCoframeMatterPrincipal coframe coordinate)) =
      ∑ internal : LorentzianIndex,
        (frameConjugateMatterDerivative coframe coordinateDerivative internal
          ).comp (identityCoframeMatterPrincipal internal) := by
  unfold frameConjugateMatterDerivative
  apply LinearMap.ext
  intro matter
  simp_rw [liveCoframeMatterPrincipal_eq_frame_sum]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  rw [Finset.sum_comm]

/-- The coframe-native time covector carries exactly the fixed internal-time
adjoint principal. -/
theorem coframeNativeTemporalAdjointPrincipal_eq
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeCovectorMatterPrincipal coframe
        (coframeNativeTemporalCovector coframe) =
      identityCoframeMatterPrincipal canonicalLorentzianTimeDirection := by
  simpa [identityCoframeMatterPrincipal,
    canonicalLorentzianTimeDirection] using
    coframeNativeTemporalMatterPrincipal_eq coframe nondegenerate

/-! ## Holonomic frame readout and action law -/

def holonomicFrameConjugateMatterDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (internal : LorentzianIndex) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  frameConjugateMatterDerivative (configuration.coframe point)
    (holonomicConjugateMatterDerivativeDual configuration point) internal

/-- All coframe/density derivatives of the densitized principal.  Both the
spatial and temporal drift terms of the live action are retained. -/
def holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  matterDualOfCoordinates
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates configuration point) +
    matterDualOfCoordinates
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates configuration point)

/-- Every action-known term except the internal frame-time adjoint
derivative. -/
def holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualLiveCoframeAlgebraicDual configuration point -
    ((generatedVolumeDensity
        (toContinuumPointField configuration point) : ℂ) •
      ∑ spatial : Fin 3,
        (holonomicFrameConjugateMatterDerivative configuration point
          spatial.succ).comp
            (identityCoframeMatterPrincipal spatial.succ)) -
    holonomicLiveCoframeTotalDensitizedPrincipalDriftDual configuration point

/-- Densitized frame-time adjoint action law. -/
def HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeFrameDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  ((generatedVolumeDensity
      (toContinuumPointField configuration point) : ℂ) •
    timeFrameDerivative.comp
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)) =
    holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
      configuration point

/-- The frame-time derivative selected by the action-owned internal-time
principal. -/
def holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (((generatedVolumeDensity
      (toContinuumPointField configuration point) : ℂ)⁻¹) •
    holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
      configuration point).comp
    (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

theorem
    holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity_satisfies
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      configuration point
      (holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
        configuration point) := by
  have volumeNeReal :
      generatedVolumeDensity
          (toContinuumPointField configuration point) ≠ 0 := by
    unfold generatedVolumeDensity toContinuumPointField
    exact abs_ne_zero.mpr nondegenerate
  have volumeNeComplex :
      (generatedVolumeDensity
        (toContinuumPointField configuration point) : ℂ) ≠ 0 := by
    exact_mod_cast volumeNeReal
  unfold HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
  apply LinearMap.ext
  intro matter
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [identityCoframeMatterPrincipal_time_involutive]
  simp [volumeNeComplex]

/-- The frame-time action solve has no hidden branch. -/
theorem
    holonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw_unique
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
        configuration point first)
    (secondLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
        configuration point second) :
    first = second := by
  have volumeNeReal :
      generatedVolumeDensity
          (toContinuumPointField configuration point) ≠ 0 := by
    unfold generatedVolumeDensity toContinuumPointField
    exact abs_ne_zero.mpr nondegenerate
  have volumeNeComplex :
      (generatedVolumeDensity
        (toContinuumPointField configuration point) : ℂ) ≠ 0 := by
    exact_mod_cast volumeNeReal
  have composedEqual :
      first.comp
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) =
        second.comp
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) := by
    apply LinearMap.ext
    intro matter
    have equality := LinearMap.congr_fun (firstLaw.trans secondLaw.symm) matter
    simp only [LinearMap.smul_apply] at equality
    exact mul_left_cancel₀ volumeNeComplex equality
  apply LinearMap.ext
  intro matter
  calc
    first matter =
        first
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
              matter)) := by
      rw [identityCoframeMatterPrincipal_time_involutive]
    _ = second
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
              matter)) := by
      exact LinearMap.congr_fun composedEqual
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection matter)
    _ = second matter := by
      rw [identityCoframeMatterPrincipal_time_involutive]

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeConjugateMatterFrameAction
