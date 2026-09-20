import H0mework.Physics.IdentityGerms.IdentityECCurvatureNormalSection
import H0mework.Physics.Gauge.GaugeWedge

/-!
# Nondegenerate-coframe EC curvature normal section

The repaired Dirac-dual mother action observes raw gravity curvature through
the metric-free pairing

```text
h ↦ W22 (D II+(e)[h]) (N F).
```

At a nondegenerate coframe, the actual exterior-square coframe action
canonically conjugates this observation to the already proved identity
normal section.  This module performs that conjugation explicitly.  It
accepts only the coframe, its nondegeneracy, the current curvature, and an
action-generated coframe covector.  No residual coordinate, target
curvature, inverse witness, representative, branch, equation, or
stationarity receipt is an input.

The historical coordinate formula remains confined to the identity normal
section, where its equality with the current topological mother-action
pairing is already proved.  No historical linear-Plebanski action semantics
are reused here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeECCurvatureNormalSection

open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeTwoFormPairing
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Exterior-square transport -/

/-- Apply the exterior-square coframe map to every spacetime two-form row of
an internal-bivector-valued two-form. -/
def physicalBivectorSpacetimeCoframeTwoFormLinear
    (coframe : LorentzianCoframe)
    (bivector : PhysicalBivector) :
    PhysicalBivector :=
  fun internalPair =>
    coframeTwoFormLinear coframe (bivector internalPair)

theorem physicalBivectorSpacetimeCoframeTwoFormLinear_add
    (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    physicalBivectorSpacetimeCoframeTwoFormLinear coframe (first + second) =
      physicalBivectorSpacetimeCoframeTwoFormLinear coframe first +
        physicalBivectorSpacetimeCoframeTwoFormLinear coframe second := by
  funext internalPair spacetimePair
  simp [physicalBivectorSpacetimeCoframeTwoFormLinear]

theorem physicalBivectorSpacetimeCoframeTwoFormLinear_smul
    (coframe : LorentzianCoframe)
    (parameter : ℝ)
    (bivector : PhysicalBivector) :
    physicalBivectorSpacetimeCoframeTwoFormLinear coframe
        (parameter • bivector) =
      parameter •
        physicalBivectorSpacetimeCoframeTwoFormLinear coframe bivector := by
  funext internalPair spacetimePair
  simp [physicalBivectorSpacetimeCoframeTwoFormLinear]

theorem
    physicalBivectorSpacetimeCoframeTwoFormLinear_varianceNormalization
    (coframe : LorentzianCoframe)
    (bivector : PhysicalBivector) :
    physicalBivectorSpacetimeCoframeTwoFormLinear coframe
        (gravityInternalPairVarianceNormalization bivector) =
      gravityInternalPairVarianceNormalization
        (physicalBivectorSpacetimeCoframeTwoFormLinear coframe bivector) := by
  funext internalPair spacetimePair
  unfold physicalBivectorSpacetimeCoframeTwoFormLinear
    coframeTwoFormLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk,
    gravityInternalPairVarianceNormalization_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem physicalBivectorSpacetimeCoframeTwoFormLinear_push_pull
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (bivector : PhysicalBivector) :
    physicalBivectorSpacetimeCoframeTwoFormLinear coframe.transpose
        (physicalBivectorSpacetimeCoframeTwoFormLinear
          (coframe⁻¹).transpose bivector) =
      bivector := by
  funext internalPair spacetimePair
  change
    ((coframeTwoFormLinear coframe.transpose).comp
      (coframeTwoFormLinear (coframe⁻¹).transpose))
        (bivector internalPair) spacetimePair =
      bivector internalPair spacetimePair
  rw [← coframeTwoFormLinear_mul, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul coframe
      (isUnit_iff_ne_zero.mpr nondegenerate)]
  simp [coframeTwoFormLinear_one]

theorem physicalBivectorSpacetimeCoframeTwoFormLinear_pull_push
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (bivector : PhysicalBivector) :
    physicalBivectorSpacetimeCoframeTwoFormLinear (coframe⁻¹).transpose
        (physicalBivectorSpacetimeCoframeTwoFormLinear
          coframe.transpose bivector) =
      bivector := by
  funext internalPair spacetimePair
  change
    ((coframeTwoFormLinear (coframe⁻¹).transpose).comp
      (coframeTwoFormLinear coframe.transpose))
        (bivector internalPair) spacetimePair =
      bivector internalPair spacetimePair
  rw [← coframeTwoFormLinear_mul, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv coframe
      (isUnit_iff_ne_zero.mpr nondegenerate)]
  simp [coframeTwoFormLinear_one]

/-- Metric-free gravity wedge covariance under the common spacetime
exterior-square coframe action. -/
theorem gravityTopologicalWedgeCoefficient_spacetimeCoframeTwoFormLinear
    (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient
        (physicalBivectorSpacetimeCoframeTwoFormLinear coframe first)
        (physicalBivectorSpacetimeCoframeTwoFormLinear coframe second) =
      coframeTwoFormWedgeScale coframe *
        gravityTopologicalWedgeCoefficient first second := by
  unfold gravityTopologicalWedgeCoefficient
    physicalBivectorSpacetimeCoframeTwoFormLinear
  simp_rw [orientedTwoFormWedgeCoefficient_coframeTwoFormLinear]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro internalPair _
  ring

/-- The physical `D II+` tangent at `e` is the identity tangent transported
by the actual exterior-square coframe action. -/
theorem physicalIIPlusCoframeTangent_mul_right
    (relative coframe : LorentzianCoframe) :
    physicalIIPlusCoframeTangent coframe (relative * coframe) =
      physicalBivectorSpacetimeCoframeTwoFormLinear coframe.transpose
        (physicalIIPlusCoframeTangent
          (1 : LorentzianCoframe) relative) := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      physicalBivectorSpacetimeCoframeTwoFormLinear,
      coframeTwoFormLinear, coframeWedge, internalBivectorDual,
      lorentzianCoframeHodge, pairFirst, pairSecond,
      Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_four, Fin.sum_univ_six] <;>
    ring

/-! ## Coframe-relative observation -/

private theorem physicalIIPlusCoframeTangent_add
    (coframe first second : LorentzianCoframe) :
    physicalIIPlusCoframeTangent coframe (first + second) =
      physicalIIPlusCoframeTangent coframe first +
        physicalIIPlusCoframeTangent coframe second := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      internalBivectorDual, lorentzianCoframeHodge,
      pairFirst, pairSecond] <;>
    ring

private theorem physicalIIPlusCoframeTangent_smul
    (coframe variation : LorentzianCoframe)
    (parameter : ℝ) :
    physicalIIPlusCoframeTangent coframe (parameter • variation) =
      parameter • physicalIIPlusCoframeTangent coframe variation := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      internalBivectorDual, lorentzianCoframeHodge,
      pairFirst, pairSecond] <;>
    ring

/-- Current-root EC curvature observation at an arbitrary coframe. -/
def coframeDiracDualECCurvatureObservation
    (coframe : LorentzianCoframe)
    (rawCurvature : PhysicalBivector) :
    LorentzianCoframe →L[ℝ] ℝ :=
  ({ toFun := fun variation =>
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (gravityInternalPairVarianceNormalization rawCurvature)
     map_add' := by
       intro first second
       rw [physicalIIPlusCoframeTangent_add,
         gravityTopologicalWedgeCoefficient_add_left]
     map_smul' := by
       intro parameter variation
       rw [physicalIIPlusCoframeTangent_smul,
         gravityTopologicalWedgeCoefficient_smul_left]
       rfl } : LorentzianCoframe →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem coframeDiracDualECCurvatureObservation_apply
    (coframe : LorentzianCoframe)
    (rawCurvature : PhysicalBivector)
    (variation : LorentzianCoframe) :
    coframeDiracDualECCurvatureObservation
        coframe rawCurvature variation =
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (gravityInternalPairVarianceNormalization rawCurvature) :=
  rfl

theorem coframeDiracDualECCurvatureObservation_add
    (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    coframeDiracDualECCurvatureObservation coframe (first + second) =
      coframeDiracDualECCurvatureObservation coframe first +
        coframeDiracDualECCurvatureObservation coframe second := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (gravityInternalPairVarianceNormalization (first + second)) =
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent coframe variation)
          (gravityInternalPairVarianceNormalization first) +
        gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent coframe variation)
          (gravityInternalPairVarianceNormalization second)
  rw [map_add, gravityTopologicalWedgeCoefficient_add_right]

@[simp] theorem coframeDiracDualECCurvatureObservation_zero
    (coframe : LorentzianCoframe) :
    coframeDiracDualECCurvatureObservation coframe 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (gravityInternalPairVarianceNormalization 0) =
      0
  simp

theorem coframeDiracDualECCurvatureObservation_sub
    (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    coframeDiracDualECCurvatureObservation coframe (first - second) =
      coframeDiracDualECCurvatureObservation coframe first -
        coframeDiracDualECCurvatureObservation coframe second := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (gravityInternalPairVarianceNormalization (first - second)) =
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent coframe variation)
          (gravityInternalPairVarianceNormalization first) -
        gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent coframe variation)
          (gravityInternalPairVarianceNormalization second)
  rw [map_sub]
  rw [show
      gravityInternalPairVarianceNormalization first -
          gravityInternalPairVarianceNormalization second =
        gravityInternalPairVarianceNormalization first +
          (-1 : ℝ) •
            gravityInternalPairVarianceNormalization second by
      module]
  rw [gravityTopologicalWedgeCoefficient_add_right,
    gravityTopologicalWedgeCoefficient_smul_right]
  ring

/-- Right multiplication of a coframe variation by a fixed coframe. -/
def coframeRightMultiplication
    (coframe : LorentzianCoframe) :
    LorentzianCoframe →L[ℝ] LorentzianCoframe :=
  ({ toFun := fun variation => variation * coframe
     map_add' := by
       intro first second
       ext row column
       simp only [Matrix.add_apply, Matrix.mul_apply]
       rw [← Finset.sum_add_distrib]
       apply Finset.sum_congr rfl
       intro index _
       ring
     map_smul' := by
       intro parameter variation
       ext row column
       simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
         RingHom.id_apply]
       rw [Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro index _
       ring } : LorentzianCoframe →ₗ[ℝ] LorentzianCoframe
    ).toContinuousLinearMap

/-- Raw curvature expressed in the identity-contact observation chart. -/
def coframeRelativeDiracDualECCurvature
    (coframe : LorentzianCoframe)
    (rawCurvature : PhysicalBivector) :
    PhysicalBivector :=
  coframeTwoFormWedgeScale coframe.transpose •
    gravityInternalPairVarianceNormalization
      (physicalBivectorSpacetimeCoframeTwoFormLinear
        (coframe⁻¹).transpose
        (gravityInternalPairVarianceNormalization rawCurvature))

/-- Exact conjugacy between the arbitrary-coframe EC observation and the
identity observation. -/
theorem coframeDiracDualECCurvatureObservation_eq_identityRelative
    (coframe : LorentzianCoframe)
    (rawCurvature : PhysicalBivector)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (variation : LorentzianCoframe) :
    coframeDiracDualECCurvatureObservation
        coframe rawCurvature variation =
      identityDiracDualECCurvatureObservation
        (coframeRelativeDiracDualECCurvature coframe rawCurvature)
        (variation * coframe⁻¹) := by
  have recoverVariation :
      (variation * coframe⁻¹) * coframe = variation := by
    rw [Matrix.mul_assoc,
      Matrix.nonsing_inv_mul coframe
        (isUnit_iff_ne_zero.mpr nondegenerate),
      Matrix.mul_one]
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (gravityInternalPairVarianceNormalization rawCurvature) =
      _
  conv_lhs =>
    lhs
    rw [← recoverVariation, physicalIIPlusCoframeTangent_mul_right]
  have pushPull :=
    physicalBivectorSpacetimeCoframeTwoFormLinear_push_pull
      coframe nondegenerate
      (gravityInternalPairVarianceNormalization rawCurvature)
  conv_lhs =>
    rhs
    rw [← pushPull]
  rw [gravityTopologicalWedgeCoefficient_spacetimeCoframeTwoFormLinear]
  change
    _ =
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent
          (1 : LorentzianCoframe) (variation * coframe⁻¹))
        (gravityInternalPairVarianceNormalization
          (coframeRelativeDiracDualECCurvature
            coframe rawCurvature))
  unfold coframeRelativeDiracDualECCurvature
  rw [map_smul, gravityInternalPairVarianceNormalization_involutive]
  rw [gravityTopologicalWedgeCoefficient_smul_right]

/-! ## Canonical normal section and faithful target -/

/-- Canonical curvature at `coframe` corresponding to an identity-chart raw
curvature.  The scale inverse and exterior-square pushforward are completely
determined by the coframe. -/
def coframeDiracDualECCurvatureOfRelative
    (coframe : LorentzianCoframe)
    (relativeCurvature : PhysicalBivector) :
    PhysicalBivector :=
  gravityInternalPairVarianceNormalization
    ((coframeTwoFormWedgeScale coframe.transpose)⁻¹ •
      physicalBivectorSpacetimeCoframeTwoFormLinear coframe.transpose
        (gravityInternalPairVarianceNormalization relativeCurvature))

/-- Pull an actual coframe covector back to the identity variation chart. -/
def coframeRelativeECCovector
    (coframe : LorentzianCoframe)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    LorentzianCoframe →L[ℝ] ℝ :=
  observation.comp (coframeRightMultiplication coframe)

/-- Canonical action-normal curvature section at any nondegenerate coframe.
The nondegeneracy proof is an admissibility argument only; proof irrelevance
prevents it from carrying a branch choice. -/
def coframeDiracDualECCurvatureNormalSection
    (coframe : LorentzianCoframe)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    PhysicalBivector :=
  coframeDiracDualECCurvatureOfRelative coframe
    (identityDiracDualECCurvatureNormalSection
      (coframeRelativeECCovector coframe observation))

/-- At the identity coframe, the transported normal section reduces exactly
to the identity-contact section. -/
theorem coframeDiracDualECCurvatureNormalSection_one
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    coframeDiracDualECCurvatureNormalSection
        (1 : LorentzianCoframe) observation =
      identityDiracDualECCurvatureNormalSection observation := by
  have relativeCovector :
      coframeRelativeECCovector (1 : LorentzianCoframe) observation =
        observation := by
    apply ContinuousLinearMap.ext
    intro variation
    change observation (variation * (1 : LorentzianCoframe)) =
      observation variation
    rw [Matrix.mul_one]
  have wedgeScale :
      coframeTwoFormWedgeScale (1 : LorentzianCoframe) = 1 := by
    simp [coframeTwoFormWedgeScale, coframeTwoFormLinear_one,
      orientedTwoFormWedgeCoefficient_basis_zero_three]
  unfold coframeDiracDualECCurvatureNormalSection
    coframeDiracDualECCurvatureOfRelative
    physicalBivectorSpacetimeCoframeTwoFormLinear
  rw [relativeCovector, Matrix.transpose_one, wedgeScale, inv_one, one_smul]
  ext internalPair spacetimePair
  simp only [coframeTwoFormLinear_one, LinearMap.id_apply]
  exact congrFun (congrFun
    (gravityInternalPairVarianceNormalization_involutive
      (identityDiracDualECCurvatureNormalSection observation))
    internalPair) spacetimePair

theorem coframeRelativeDiracDualECCurvature_ofRelative
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (relativeCurvature : PhysicalBivector) :
    coframeRelativeDiracDualECCurvature coframe
        (coframeDiracDualECCurvatureOfRelative
          coframe relativeCurvature) =
      relativeCurvature := by
  have scaleNonzero :
      coframeTwoFormWedgeScale coframe.transpose ≠ 0 := by
    apply coframeTwoFormWedgeScale_ne_zero
    simpa [Matrix.det_transpose] using nondegenerate
  unfold coframeRelativeDiracDualECCurvature
    coframeDiracDualECCurvatureOfRelative
  rw [gravityInternalPairVarianceNormalization_involutive]
  rw [physicalBivectorSpacetimeCoframeTwoFormLinear_smul]
  rw [physicalBivectorSpacetimeCoframeTwoFormLinear_pull_push
    coframe nondegenerate]
  rw [map_smul, gravityInternalPairVarianceNormalization_involutive]
  rw [smul_smul, mul_inv_cancel₀ scaleNonzero, one_smul]

/-- **Positive arbitrary-contact frontier.**  The coframe-relative section is
a genuine right inverse of the actual mother-action EC observation. -/
theorem coframeDiracDualECCurvatureObservation_normalSection
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    coframeDiracDualECCurvatureObservation coframe
        (coframeDiracDualECCurvatureNormalSection
          coframe observation) =
      observation := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [coframeDiracDualECCurvatureObservation_eq_identityRelative
    coframe _ nondegenerate variation]
  unfold coframeDiracDualECCurvatureNormalSection
  rw [coframeRelativeDiracDualECCurvature_ofRelative
    coframe nondegenerate]
  rw [identityDiracDualECCurvatureObservation_normalSection]
  change observation ((variation * coframe⁻¹) * coframe) =
    observation variation
  rw [Matrix.mul_assoc,
    Matrix.nonsing_inv_mul coframe
      (isUnit_iff_ne_zero.mpr nondegenerate),
    Matrix.mul_one]

theorem coframeDiracDualECCurvatureNormalSection_injective
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Injective
      (coframeDiracDualECCurvatureNormalSection coframe) := by
  intro first second equality
  have observed := congrArg
    (coframeDiracDualECCurvatureObservation coframe) equality
  simpa only [
    coframeDiracDualECCurvatureObservation_normalSection
      coframe nondegenerate] using observed

/-- Current curvature responsibility invisible to the EC coframe equation at
the actual coframe. -/
def coframeDiracDualECCurvatureKernelPart
    (coframe : LorentzianCoframe)
    (rawCurvature : PhysicalBivector) :
    PhysicalBivector :=
  rawCurvature -
    coframeDiracDualECCurvatureNormalSection coframe
      (coframeDiracDualECCurvatureObservation
        coframe rawCurvature)

theorem coframeDiracDualECCurvatureObservation_kernelPart
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (rawCurvature : PhysicalBivector) :
    coframeDiracDualECCurvatureObservation coframe
        (coframeDiracDualECCurvatureKernelPart
          coframe rawCurvature) =
      0 := by
  rw [coframeDiracDualECCurvatureKernelPart,
    coframeDiracDualECCurvatureObservation_sub,
    coframeDiracDualECCurvatureObservation_normalSection
      coframe nondegenerate]
  abel

/-- Replace only the action-observed EC component and retain the complete
current kernel component. -/
def coframeDiracDualECCurvatureTarget
    (coframe : LorentzianCoframe)
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    PhysicalBivector :=
  coframeDiracDualECCurvatureKernelPart coframe current +
    coframeDiracDualECCurvatureNormalSection coframe observation

/-- At identity coframe the transported faithful target is exactly the
identity-contact target. -/
theorem coframeDiracDualECCurvatureTarget_one
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    coframeDiracDualECCurvatureTarget
        (1 : LorentzianCoframe) current observation =
      identityDiracDualECCurvatureTarget current observation := by
  unfold coframeDiracDualECCurvatureTarget
    coframeDiracDualECCurvatureKernelPart
    identityDiracDualECCurvatureTarget
    identityDiracDualECCurvatureKernelPart
  simp_rw [coframeDiracDualECCurvatureNormalSection_one]
  rfl

theorem coframeDiracDualECCurvatureObservation_target
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    coframeDiracDualECCurvatureObservation coframe
        (coframeDiracDualECCurvatureTarget
          coframe current observation) =
      observation := by
  rw [coframeDiracDualECCurvatureTarget,
    coframeDiracDualECCurvatureObservation_add,
    coframeDiracDualECCurvatureObservation_kernelPart
      coframe nondegenerate,
    coframeDiracDualECCurvatureObservation_normalSection
      coframe nondegenerate,
    zero_add]

theorem coframeDiracDualECCurvatureKernelPart_target
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    coframeDiracDualECCurvatureKernelPart coframe
        (coframeDiracDualECCurvatureTarget
          coframe current observation) =
      coframeDiracDualECCurvatureKernelPart coframe current := by
  unfold coframeDiracDualECCurvatureKernelPart
  rw [coframeDiracDualECCurvatureObservation_target
    coframe nondegenerate]
  change
    (coframeDiracDualECCurvatureKernelPart coframe current +
        coframeDiracDualECCurvatureNormalSection coframe observation) -
        coframeDiracDualECCurvatureNormalSection coframe observation =
      coframeDiracDualECCurvatureKernelPart coframe current
  abel

/-- Branch-free target uniqueness relative to the current action-normal
kernel responsibility. -/
theorem coframeDiracDualECCurvatureTarget_unique
    (coframe : LorentzianCoframe)
    (current candidate : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ)
    (hObservation :
      coframeDiracDualECCurvatureObservation coframe candidate =
        observation)
    (hKernel :
      coframeDiracDualECCurvatureKernelPart coframe candidate =
        coframeDiracDualECCurvatureKernelPart coframe current) :
    candidate =
      coframeDiracDualECCurvatureTarget
        coframe current observation := by
  calc
    candidate =
        coframeDiracDualECCurvatureKernelPart coframe candidate +
          coframeDiracDualECCurvatureNormalSection coframe
            (coframeDiracDualECCurvatureObservation
              coframe candidate) := by
      unfold coframeDiracDualECCurvatureKernelPart
      abel
    _ = coframeDiracDualECCurvatureKernelPart coframe current +
          coframeDiracDualECCurvatureNormalSection
            coframe observation := by
      rw [hKernel, hObservation]
    _ = coframeDiracDualECCurvatureTarget
          coframe current observation := rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
