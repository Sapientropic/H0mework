import H0mework.Versions.V2.Arithmetic.MobiusSource.FirstCell
import H0mework.Versions.V2.Arithmetic.SonineProjection.ProjectionFormula
import H0mework.Versions.V2.Arithmetic.RiemannSpectral.PaOrthogonalCompression

/-! Two source-generated interval fields drive the complete paired projection. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

/-- The full projected action is forced by the same extracted source in its
first cell.  The other window is an actual constant gap, hence zero only in
the installed mean-zero face. -/
def burnolFirstCellProjectionBlockSource (shift : ℝ) (value : Ambient) :
    BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier :=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
    (burnolQuarterRestriction (burnolMultiplicativeDilation shift
      (burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value)))), 0)

theorem burnolFirstCellProjectionBlockSource_eq (shift : ℝ)
    (nonnegative : 0 ≤ shift) (small : shift ≤ Real.log 2) (value : Ambient) :
    burnolFirstCellProjectionBlockSource shift value =
      burnolAmbientMeanZeroBlockRhs
        (burnolMultiplicativeDilation shift (value : BurnolL2)) := by
  have valueEven : burnolAmbientEvenPart
      (burnolMultiplicativeDilation shift (value : BurnolL2)) =
        burnolMultiplicativeDilation shift (value : BurnolL2) := by
    have fixed := mem_evenL2ClosedFace_iff.mp
      (burnolMultiplicativeDilation_mem_evenL2ClosedFace shift (value : BurnolL2)
        value.property.2)
    unfold burnolAmbientEvenPart
    rw [fixed]
    module
  unfold burnolFirstCellProjectionBlockSource burnolAmbientMeanZeroBlockRhs
    burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier
  rw [valueEven]
  apply Prod.ext
  · apply Subtype.ext
    exact burnolMobiusSourceDilation_meanZero shift small value
  · apply Subtype.ext
    change 0 = burnolQuarterMeanZeroProjection
      (burnolQuarterRestriction (fourierL2
        (burnolMultiplicativeDilation shift (value : BurnolL2))))
    symm
    rw [fourierL2_burnolMultiplicativeDilation]
    apply (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
    exact burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive
      q (by norm_num) (-shift) (neg_nonpos.mpr nonnegative)
      (fourierL2 (value : BurnolL2)) value.property.1.2


def burnolFirstCellCorrection (shift : ℝ) (value : Ambient) :
    BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroBlockInverse (burnolFirstCellProjectionBlockSource shift value).1

theorem burnolFirstCellCorrection_block (shift : ℝ) (value : Ambient) :
    burnolMeanZeroBlockFirst (burnolFirstCellProjectionBlockSource shift value) =
      burnolFirstCellCorrection shift value ∧
    burnolMeanZeroBlockSecond (burnolFirstCellProjectionBlockSource shift value) =
      -burnolMeanZeroTruncatedFourier (burnolFirstCellCorrection shift value) := by
  constructor
  · simp [burnolMeanZeroBlockFirst, burnolFirstCellCorrection,
      burnolFirstCellProjectionBlockSource]
  · simp [burnolMeanZeroBlockSecond, burnolMeanZeroBlockFirst,
      burnolFirstCellCorrection, burnolFirstCellProjectionBlockSource]

/-- A single source-generated interval field drives the full unchanged
projection, including its Fourier correction. No Pa input/output membership
is supplied to this actual small-scale action. -/
theorem burnolFirstCellProjection_formula (shift : ℝ)
    (nonnegative : 0 ≤ shift) (small : shift ≤ Real.log 2) (value : Ambient) :
    let b := burnolFirstCellCorrection shift value
    (evenBurnolClosedFace q).toSubmodule.starProjection
      (burnolMultiplicativeDilation shift (value : BurnolL2)) =
        burnolMultiplicativeDilation shift (value : BurnolL2) -
          burnolAmbientEvenPart
            (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2) -
              fourierL2 (burnolQuarterZeroExtension
                (burnolMeanZeroTruncatedFourier b : BurnolQuarterIntervalL2))) := by
  dsimp only
  have valueEven : burnolAmbientEvenPart
      (burnolMultiplicativeDilation shift (value : BurnolL2)) =
        burnolMultiplicativeDilation shift (value : BurnolL2) := by
    have fixed := mem_evenL2ClosedFace_iff.mp
      (burnolMultiplicativeDilation_mem_evenL2ClosedFace shift (value : BurnolL2)
        value.property.2)
    unfold burnolAmbientEvenPart
    rw [fixed]
    module
  rw [burnolEvenOrthogonalProjection_eq_resolventFormula]
  unfold burnolAmbientExtendedSonineProjectionFormula
    burnolAmbientEvenMeanZeroCorrection burnolAmbientRawMeanZeroCorrection
    burnolAmbientMeanZeroFirstCorrection burnolAmbientMeanZeroSecondCorrection
  rw [← burnolFirstCellProjectionBlockSource_eq shift nonnegative small value,
    (burnolFirstCellCorrection_block shift value).1,
    (burnolFirstCellCorrection_block shift value).2, valueEven]
  simp only [Submodule.coe_neg, map_neg, sub_eq_add_neg]

/-- The entire position/Fourier correction, generated by the first source
cell rather than supplied as a boundary datum. -/
def burnolFirstCellCorrectionField (shift : ℝ) (value : Ambient) : BurnolL2 :=
  let b := burnolFirstCellCorrection shift value
  burnolAmbientEvenPart
    (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2) -
      fourierL2 (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier b : BurnolQuarterIntervalL2)))

theorem burnolFirstCellInverseProjection_formula (shift : ℝ)
    (nonnegative : 0 ≤ shift) (small : shift ≤ Real.log 2) (value : Ambient) :
    (evenBurnolClosedFace q).toSubmodule.starProjection
      (burnolMultiplicativeDilation (-shift) (value : BurnolL2)) =
        burnolMultiplicativeDilation (-shift) (value : BurnolL2) -
          fourierL2 (burnolFirstCellCorrectionField shift
            (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)) := by
  have generated := congrArg fourierL2
    (burnolFirstCellProjection_formula shift nonnegative small
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value))
  have twice : fourierL2
      ((evenFaceFourierEquiv burnolUnscaledCommonGapRadius value : Ambient) : BurnolL2) =
        (value : BurnolL2) := by
    change fourierL2 (fourierL2 (value : BurnolL2)) = _
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp value.property.2
  change fourierL2 (evenBurnolPhysicalProjection q
      (burnolMultiplicativeDilation shift
        ((evenFaceFourierEquiv burnolUnscaledCommonGapRadius value : Ambient) : BurnolL2))) =
    fourierL2 (burnolMultiplicativeDilation shift
        ((evenFaceFourierEquiv burnolUnscaledCommonGapRadius value : Ambient) : BurnolL2) -
      burnolFirstCellCorrectionField shift
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)) at generated
  rw [fourierL2_evenBurnolPhysicalProjection, map_sub,
    fourierL2_burnolMultiplicativeDilation, twice] at generated
  exact generated

/-- The two source-generated interval fields are the complete correction of
the actual paired compression.  Fourier is applied to the sibling's whole
field, so neither constant mode nor either correction is discarded. -/
theorem burnolFirstCellPairedProjection_formula (shift : ℝ)
    (nonnegative : 0 ≤ shift) (small : shift ≤ Real.log 2) (value : Ambient) :
    (burnolPairedAmbientCompression shift value : BurnolL2) =
      pairedBurnolMultiplicativeDilation shift (value : BurnolL2) -
        (1 / 2 : ℂ) •
          (burnolFirstCellCorrectionField shift value +
            fourierL2 (burnolFirstCellCorrectionField shift
              (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value))) := by
  change (1 / 2 : ℂ) •
      ((evenBurnolClosedFace q).toSubmodule.starProjection
          (burnolMultiplicativeDilation shift (value : BurnolL2)) +
        (evenBurnolClosedFace q).toSubmodule.starProjection
          (burnolMultiplicativeDilation (-shift) (value : BurnolL2))) = _
  rw [burnolFirstCellInverseProjection_formula shift nonnegative small value,
    burnolFirstCellProjection_formula shift nonnegative small value]
  change (1 / 2 : ℂ) •
      ((burnolMultiplicativeDilation shift (value : BurnolL2) -
          burnolFirstCellCorrectionField shift value) +
        (burnolMultiplicativeDilation (-shift) (value : BurnolL2) -
          fourierL2 (burnolFirstCellCorrectionField shift
            (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)))) = _
  simp only [pairedBurnolMultiplicativeDilation, smul_apply, add_apply,
    ContinuousLinearEquiv.coe_coe, smul_sub, smul_add]
  change (1 / 2 : ℂ) • burnolMultiplicativeDilation shift (value : BurnolL2) -
      (1 / 2 : ℂ) • burnolFirstCellCorrectionField shift value +
      ((1 / 2 : ℂ) • burnolMultiplicativeDilation (-shift) (value : BurnolL2) -
        (1 / 2 : ℂ) • fourierL2 (burnolFirstCellCorrectionField shift
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value))) =
    (1 / 2 : ℂ) • burnolMultiplicativeDilation shift (value : BurnolL2) +
      (1 / 2 : ℂ) • burnolMultiplicativeDilation (-shift) (value : BurnolL2) -
      ((1 / 2 : ℂ) • burnolFirstCellCorrectionField shift value +
        (1 / 2 : ℂ) • fourierL2 (burnolFirstCellCorrectionField shift
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)))
  abel

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
