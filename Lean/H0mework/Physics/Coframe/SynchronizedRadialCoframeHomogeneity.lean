import H0mework.Physics.Coframe.ResidualLimitCoframePointCarrierTransportBoundary

/-!
# S9-C3h63b: synchronized radial coframe homogeneity

This module records the scaling laws needed to transport independently
generated coframe-stress projections from the reference coframe to the
existing-field synchronized radial carrier.  The laws are consequences of
the declared action densities; they do not select a radial scalar or carry a
target solution in source data.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineSynchronizedRadialCoframeHomogeneity

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeLocalDifferentiability
open StageNineCoframeSectorStress
open StageNineCoframeVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineResidualLimitCoframeBalanceDecision
open StageNineResidualLimitCoframePointCarrierTransportBoundary
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- At a fixed candidate coframe, synchronizing the two gravity two-forms
scales the actual BF density by the forced fourth power. -/
theorem synchronizedRadialPointField_gravityBFDensity_eq_reference
    (scalar : ℝ) (candidate : LorentzianCoframe) :
    generatedGravityBFDensity
        (withCoframe (synchronizedRadialPointField scalar) candidate) =
      scalar ^ 4 *
        generatedGravityBFDensity
          (withCoframe referenceOriginField candidate) := by
  unfold generatedGravityBFDensity
  simp only [withCoframe, synchronizedRadialPointField]
  rw [gravityInternalDualEquiv.map_smul]
  simp_rw [gravitySpacetimeHodge_smul]
  rw [gravityCoframePairing_smul_left,
    gravityCoframePairing_smul_right,
    gravityCoframePairing_smul_left,
    gravityCoframePairing_smul_right]
  ring

theorem synchronizedRadialPointField_gravitySectorDensity_eq_reference
    (scalar : ℝ) (candidate : LorentzianCoframe) :
    coframeGravitySectorLocalDensity
        (synchronizedRadialPointField scalar) candidate =
      scalar ^ 4 *
        coframeGravitySectorLocalDensity referenceOriginField candidate := by
  unfold coframeGravitySectorLocalDensity
  rw [generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero
      (withCoframe (synchronizedRadialPointField scalar) candidate),
    generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero
      (withCoframe referenceOriginField candidate),
    synchronizedRadialPointField_gravityBFDensity_eq_reference]
  · change generatedVolumeDensity (withCoframe referenceOriginField candidate) *
        (0 + scalar ^ 4 *
          generatedGravityBFDensity
            (withCoframe referenceOriginField candidate)) = _
    ring
  · exact referencePointField_multiplier_zero
  · exact synchronizedRadialPointField_multiplier scalar

/-- The synchronized carrier retains every gauge coordinate, so at a fixed
candidate coframe its gauge-sector density is literally the reference one. -/
theorem synchronizedRadialPointField_gaugeSectorDensity_eq_reference
    (scalar : ℝ) (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        (synchronizedRadialPointField scalar) candidate =
      coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        referenceOriginField candidate := by
  rfl

/-- Inverse matrices scale contragrediently on the nondegenerate branch. -/
theorem matrix_inv_smul_of_nondegenerate
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    (scalar • coframe)⁻¹ = scalar⁻¹ • coframe⁻¹ := by
  letI : Invertible scalar := invertibleOfNonzero nonzero
  simpa only [invOf_eq_inv] using
    (Matrix.inv_smul (A := coframe) scalar
      (isUnit_iff_ne_zero.mpr nondegenerate))

theorem coframeGaugeSpacetimeHodgeLinear_smul_of_nondegenerate
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeGaugeSpacetimeHodgeLinear (scalar • coframe) =
      coframeGaugeSpacetimeHodgeLinear coframe := by
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [matrix_inv_smul_of_nondegenerate scalar nonzero coframe nondegenerate]
  rw [coframeTwoFormLinear_smul, coframeTwoFormLinear_smul]
  apply LinearMap.ext
  intro form
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [map_smul, map_smul]
  simp only [smul_smul]
  field_simp
  simp

theorem generatedVolumeDensity_withCoframe_smul
    (scalar : ℝ) (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) :
    generatedVolumeDensity (withCoframe field (scalar • coframe)) =
      scalar ^ 4 *
        generatedVolumeDensity (withCoframe field coframe) := by
  change |Matrix.det (scalar • coframe)| =
    scalar ^ 4 * |Matrix.det coframe|
  have determinantScale :
      Matrix.det (scalar • coframe) =
        scalar ^ 4 * Matrix.det coframe := by
    rw [Matrix.det_smul]
    norm_num
  calc
    |Matrix.det (scalar • coframe)| =
        |scalar ^ 4 * Matrix.det coframe| :=
      congrArg abs determinantScale
    _ = |scalar ^ 4| * |Matrix.det coframe| :=
      abs_mul _ _
    _ = scalar ^ 4 * |Matrix.det coframe| := by
      rw [abs_of_nonneg (by positivity)]

theorem coframeTwoFormMetricPairing_smul_general
    (scalar : ℝ) (coframe : LorentzianCoframe)
    (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing (scalar • coframe) first second =
      scalar ^ 4 * coframeTwoFormMetricPairing coframe first second := by
  unfold coframeTwoFormMetricPairing
  rw [coframeTwoFormLinear_smul]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem gravityCoframePairing_smul_coframe_general
    (scalar : ℝ) (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    gravityCoframePairing (scalar • coframe) first second =
      scalar ^ 4 * gravityCoframePairing coframe first second := by
  change (∑ internalPair : Fin 6,
      lorentzianTwoFormSign internalPair *
        coframeTwoFormMetricPairing (scalar • coframe)
          (first internalPair) (second internalPair)) =
    scalar ^ 4 *
      ∑ internalPair : Fin 6,
        lorentzianTwoFormSign internalPair *
          coframeTwoFormMetricPairing coframe
            (first internalPair) (second internalPair)
  simp_rw [coframeTwoFormMetricPairing_smul_general]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro internalPair _
  ring

theorem generatedGaugeTwoFormMetricPairing_smul_coframe_general
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pairing : V → V → ℝ)
    (pairing_smul_left : ∀ scalar first second,
      pairing (scalar • first) second = scalar * pairing first second)
    (pairing_smul_right : ∀ scalar first second,
      pairing first (scalar • second) = scalar * pairing first second)
    (scalar : ℝ) (coframe : LorentzianCoframe)
    (first second : Fin 6 → V) :
    generatedGaugeTwoFormMetricPairing pairing (scalar • coframe)
        first second =
      scalar ^ 4 *
        generatedGaugeTwoFormMetricPairing pairing coframe first second := by
  unfold generatedGaugeTwoFormMetricPairing
  rw [coframeTwoFormLinear_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  simp only [liftGaugeTwoFormOperator_smul_operator, Pi.smul_apply]
  rw [pairing_smul_left, pairing_smul_right]
  ring

theorem generatedGaugeSectorBFDensity_smul_coframe_general
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pairing : V → V → ℝ)
    (pairing_smul_left : ∀ scalar first second,
      pairing (scalar • first) second = scalar * pairing first second)
    (pairing_smul_right : ∀ scalar first second,
      pairing first (scalar • second) = scalar * pairing first second)
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coupling : ℝ)
    (curvature auxiliary : Fin 6 → V) :
    generatedGaugeSectorBFDensity pairing (scalar • coframe)
        (coframeGaugeSpacetimeHodgeLinear (scalar • coframe))
        (coupling • coframeGaugeSpacetimeHodgeLinear (scalar • coframe))
        curvature auxiliary =
      scalar ^ 4 *
        generatedGaugeSectorBFDensity pairing coframe
          (coframeGaugeSpacetimeHodgeLinear coframe)
          (coupling • coframeGaugeSpacetimeHodgeLinear coframe)
          curvature auxiliary := by
  rw [coframeGaugeSpacetimeHodgeLinear_smul_of_nondegenerate
    scalar nonzero coframe nondegenerate]
  unfold generatedGaugeSectorBFDensity
  rw [generatedGaugeTwoFormMetricPairing_smul_coframe_general
      pairing pairing_smul_left pairing_smul_right,
    generatedGaugeTwoFormMetricPairing_smul_coframe_general
      pairing pairing_smul_left pairing_smul_right]
  ring

theorem referenceGravityBFDensity_smul_coframe
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    generatedGravityBFDensity
        (withCoframe referenceOriginField (scalar • coframe)) =
      scalar ^ 4 *
        generatedGravityBFDensity
          (withCoframe referenceOriginField coframe) := by
  have hodgeEq :=
    coframeGaugeSpacetimeHodgeLinear_smul_of_nondegenerate
      scalar nonzero coframe nondegenerate
  unfold generatedGravityBFDensity gravitySpacetimeHodge
  simp only [withCoframe]
  rw [hodgeEq]
  rw [gravityCoframePairing_smul_coframe_general,
    gravityCoframePairing_smul_coframe_general]
  ring

theorem referenceGravitySectorDensity_degreeEight
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeGravitySectorLocalDensity referenceOriginField
        (scalar • coframe) =
      scalar ^ 8 *
        coframeGravitySectorLocalDensity referenceOriginField coframe := by
  unfold coframeGravitySectorLocalDensity
  rw [generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero,
    generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero,
    referenceGravityBFDensity_smul_coframe scalar nonzero coframe nondegenerate]
  · have volumeScale := generatedVolumeDensity_withCoframe_smul
        scalar referenceOriginField coframe
    rw [volumeScale]
    ring
  · exact referencePointField_multiplier_zero
  · exact referencePointField_multiplier_zero

theorem referenceGaugeSectorDensity_degreeEight
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        referenceOriginField (scalar • coframe) =
      scalar ^ 8 *
        coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
          referenceOriginField coframe := by
  unfold coframeGaugeSectorLocalDensity
  dsimp only
  have couplingStrongWeak :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared := rfl
  have couplingStrongHypercharge :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared := rfl
  rw [← couplingStrongWeak, ← couplingStrongHypercharge]
  rw [← generatedGaugeSectorBFDensity_p286_decompose]
  rw [generatedGaugeSectorBFDensity_p286_eq_coordinate]
  rw [positiveSource_generatedGaugeCoupling_eq_half]
  have volumeScale := generatedVolumeDensity_withCoframe_smul
      scalar referenceOriginField coframe
  rw [volumeScale]
  rw [generatedGaugeSectorBFDensity_smul_coframe_general
      p286CoordinateLiePairing
      p286CoordinateLiePairing_smul_left
      (fun parameter first second =>
        p286CoordinateLiePairing_smul_right parameter second first)]
  rw [← generatedGaugeSectorBFDensity_p286_decompose]
  rw [generatedGaugeSectorBFDensity_p286_eq_coordinate]
  ring
  all_goals assumption

/-- General derivative consequence of degree-eight homogeneity around the
identity coframe. -/
theorem fderiv_degreeEight_radial
    (density : LorentzianCoframe → ℝ)
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (scaleEventually :
      (fun coframe : LorentzianCoframe => density (scalar • coframe)) =ᶠ[nhds 1]
        (fun coframe => scalar ^ 8 * density coframe)) :
    fderiv ℝ density (radialCoframe scalar) =
      scalar ^ 7 • fderiv ℝ density (1 : LorentzianCoframe) := by
  have derivativeEquality :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) scaleEventually
  have composedDerivative :
      fderiv ℝ (fun coframe : LorentzianCoframe =>
          density (scalar • coframe)) (1 : LorentzianCoframe) =
        scalar • fderiv ℝ density (radialCoframe scalar) := by
    change fderiv ℝ
        (density ∘ fun coframe : LorentzianCoframe => scalar • coframe)
        (1 : LorentzianCoframe) =
      scalar • fderiv ℝ density (scalar • (1 : LorentzianCoframe))
    exact fderiv_comp_smul (𝕜 := ℝ) (f := density)
      (x := (1 : LorentzianCoframe)) scalar
  have scaledDerivative :
      fderiv ℝ (fun coframe : LorentzianCoframe =>
          scalar ^ 8 * density coframe) (1 : LorentzianCoframe) =
        scalar ^ 8 • fderiv ℝ density (1 : LorentzianCoframe) := by
    change fderiv ℝ (scalar ^ 8 • density) (1 : LorentzianCoframe) = _
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ)
      (f := density) (scalar ^ 8)) (1 : LorentzianCoframe)
  rw [composedDerivative, scaledDerivative] at derivativeEquality
  change scalar • fderiv ℝ density (radialCoframe scalar) =
      scalar ^ 8 • fderiv ℝ density (1 : LorentzianCoframe)
    at derivativeEquality
  apply (isUnit_iff_ne_zero.mpr nonzero).smul_left_cancel.mp
  calc
    scalar • fderiv ℝ density (radialCoframe scalar) =
        scalar ^ 8 • fderiv ℝ density (1 : LorentzianCoframe) :=
      derivativeEquality
    _ = scalar •
        (scalar ^ 7 • fderiv ℝ density (1 : LorentzianCoframe)) := by
      rw [smul_smul]
      ring_nf

end

end SaturationMonoid.PhysicsCore.StageNineSynchronizedRadialCoframeHomogeneity
