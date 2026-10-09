import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.RieszCanonicalRaw

/-!
# Canonical position raw for the even Burnol projection

Subordinate transporter only.  Starting from an actual raw representative of
one ambient value, the first block correction is reconstructed from the first
block equation.  The second correction occurs only under its canonical
finite-interval Fourier integral; no point representative of it is selected.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

def burnolMeanZeroRaw
    (value : BurnolQuarterIntervalL2) (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  raw x - burnolQuarterMeanCoefficient value

theorem burnolMeanZeroProjection_ae_raw
    (value : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] raw) :
    (burnolQuarterMeanZeroProjection value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))]
        burnolMeanZeroRaw value raw := by
  rw [burnolMeanZeroProjection_eq_sub_constant]
  filter_upwards [Lp.coeFn_sub value
      (burnolQuarterMeanCoefficient value • intervalConstant (1 / 4 : ℝ)),
    Lp.coeFn_smul (burnolQuarterMeanCoefficient value)
      (intervalConstant (1 / 4 : ℝ)), read,
    intervalConstant_coeFn (1 / 4 : ℝ)]
      with x subRead smulRead valueRead constantRead
  rw [subRead]
  change value x -
      (burnolQuarterMeanCoefficient value •
        intervalConstant (1 / 4 : ℝ) : BurnolQuarterIntervalL2) x = _
  rw [smulRead]
  change value x - burnolQuarterMeanCoefficient value *
      intervalConstant (1 / 4 : ℝ) x = _
  rw [valueRead, constantRead, mul_one]
  rfl

def burnolPositionMeanZeroRaw
    (value : BurnolL2) (raw : ℝ → ℂ) : ℝ → ℂ :=
  burnolMeanZeroRaw
    (burnolQuarterRestriction (burnolAmbientEvenPart value))
    (burnolEvenRaw raw)

theorem burnolPositionMeanZero_ae_raw
    (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ) =ᵐ[volume] raw) :
    ((burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2) :
      ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))]
        burnolPositionMeanZeroRaw value raw := by
  let evenValue := burnolAmbientEvenPart value
  have evenRead := burnolEvenRaw_ae value raw read
  have restricted :
      (burnolQuarterRestriction evenValue : ℝ → ℂ) =ᵐ[
        volume.restrict (symmetricInterval (1 / 4 : ℝ))]
          burnolEvenRaw raw :=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1 / 4 : ℝ)) evenValue).trans
      (ae_restrict_of_ae evenRead)
  change (burnolQuarterMeanZeroProjection
      (burnolQuarterRestriction evenValue) : ℝ → ℂ) =ᵐ[_] _
  exact burnolMeanZeroProjection_ae_raw _ _ restricted

def burnolFirstCorrectionRaw
    (value : BurnolL2) (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  burnolPositionMeanZeroRaw value raw x -
    burnolMeanZeroFourierRaw
      (burnolAmbientMeanZeroSecondCorrection value) x

theorem burnolFirstCorrection_ae_raw
    (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ) =ᵐ[volume] raw) :
    ((burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2) :
      ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))]
        burnolFirstCorrectionRaw value raw := by
  have block := burnolMeanZeroBlock_first_equation
    (burnolAmbientMeanZeroBlockRhs value)
  change burnolAmbientMeanZeroFirstCorrection value +
      burnolMeanZeroTruncatedFourier
        (burnolAmbientMeanZeroSecondCorrection value) =
    burnolAmbientMeanZeroPosition value at block
  have solved : burnolAmbientMeanZeroFirstCorrection value =
      burnolAmbientMeanZeroPosition value -
        burnolMeanZeroTruncatedFourier
          (burnolAmbientMeanZeroSecondCorrection value) := by
    exact eq_sub_of_add_eq block
  have solvedCoe :
      (burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2) =
        (burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2) -
          (burnolMeanZeroTruncatedFourier
            (burnolAmbientMeanZeroSecondCorrection value) :
              BurnolQuarterIntervalL2) := by
    simpa using congrArg
      (fun state : BurnolQuarterMeanZeroCarrier ↦
        (state : BurnolQuarterIntervalL2)) solved
  rw [solvedCoe]
  filter_upwards [Lp.coeFn_sub
      (burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2)
      (burnolMeanZeroTruncatedFourier
        (burnolAmbientMeanZeroSecondCorrection value) : BurnolQuarterIntervalL2),
    burnolPositionMeanZero_ae_raw value raw read,
    burnolMeanZeroFourier_ae_raw
      (burnolAmbientMeanZeroSecondCorrection value)]
      with x subRead positionRead fourierRead
  rw [subRead]
  change (burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2) x -
    (burnolMeanZeroTruncatedFourier
      (burnolAmbientMeanZeroSecondCorrection value) : BurnolQuarterIntervalL2) x = _
  rw [positionRead, fourierRead]
  rfl

private theorem burnolZeroExtensionFirst_ae_raw
    (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ) =ᵐ[volume] raw) :
    (burnolQuarterZeroExtension
        (burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2) :
      ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval (1 / 4 : ℝ)).indicator
        (burnolFirstCorrectionRaw value raw) := by
  have localRead := (ae_restrict_iff'
      (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp
    (burnolFirstCorrection_ae_raw value raw read)
  filter_upwards [burnolRadiusZeroExtension_coe
      (burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2),
    localRead] with x extended firstRead
  change burnolRadiusZeroExtension (1 / 4 : ℝ)
    (burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2) x = _
  rw [extended]
  by_cases hx : x ∈ symmetricInterval (1 / 4 : ℝ)
  · simp only [Set.indicator_of_mem hx]
    exact firstRead hx
  · simp only [Set.indicator_of_notMem hx]

def burnolRawCorrectionRaw
    (value : BurnolL2) (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  (symmetricInterval (1 / 4 : ℝ)).indicator
      (burnolFirstCorrectionRaw value raw) x +
    burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
      (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2) x

theorem burnolRawCorrection_ae_raw
    (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ) =ᵐ[volume] raw) :
    (burnolAmbientRawMeanZeroCorrection value : ℝ → ℂ) =ᵐ[volume]
      burnolRawCorrectionRaw value raw := by
  unfold burnolAmbientRawMeanZeroCorrection
  filter_upwards [Lp.coeFn_add
      (burnolQuarterZeroExtension
        (burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2))
      (fourierL2 (burnolQuarterZeroExtension
        (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2))),
    burnolZeroExtensionFirst_ae_raw value raw read,
    burnolRadiusFourierL2_zeroExtension_ae_eq_raw
      (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2)]
      with x added firstRead secondFourierRead
  rw [added]
  change burnolQuarterZeroExtension
      (burnolAmbientMeanZeroFirstCorrection value : BurnolQuarterIntervalL2) x +
    fourierL2 (burnolQuarterZeroExtension
      (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2)) x = _
  rw [firstRead]
  change _ + fourierL2 (burnolRadiusZeroExtension (1 / 4 : ℝ)
    (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2)) x = _
  rw [secondFourierRead]
  rfl

def burnolEvenProjectionRaw
    (value : BurnolL2) (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  burnolEvenRaw raw x -
    burnolEvenRaw (burnolRawCorrectionRaw value raw) x

/-- Canonical position representative of the actual even Burnol projection. -/

theorem burnolEvenProjection_ae_raw
    (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ) =ᵐ[volume] raw) :
    ((((evenBurnolClosedFace (1 / 4 : ℝ)).toSubmodule.orthogonalProjectionOnto
        value : EvenBurnolPhysicalCarrier (1 / 4 : ℝ)) : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      burnolEvenProjectionRaw value raw := by
  rw [burnolEvenOrthogonalProjectionOnto_eq_resolventFormula]
  unfold burnolAmbientExtendedSonineProjectionFormula
    burnolAmbientEvenMeanZeroCorrection
  filter_upwards [Lp.coeFn_sub (burnolAmbientEvenPart value)
      (burnolAmbientEvenPart (burnolAmbientRawMeanZeroCorrection value)),
    burnolEvenRaw_ae value raw read,
    burnolEvenRaw_ae (burnolAmbientRawMeanZeroCorrection value)
      (burnolRawCorrectionRaw value raw)
      (burnolRawCorrection_ae_raw value raw read)]
      with x subRead valueRead correctionRead
  rw [subRead]
  change burnolAmbientEvenPart value x -
    burnolAmbientEvenPart (burnolAmbientRawMeanZeroCorrection value) x = _
  rw [valueRead, correctionRead]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
