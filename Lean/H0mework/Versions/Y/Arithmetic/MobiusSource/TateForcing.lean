import H0mework.Versions.Y.Arithmetic.MobiusSource.Tate
import H0mework.Versions.Y.Arithmetic.MobiusSource.ActionProjection

/-! The Fourier forcing reads the reciprocal outer shell of the same extracted source. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace ENNReal
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

/-- Literal half-density/Jacobian read of the reciprocal forcing. -/
theorem burnolSourceReciprocal_dilation_raw (shift : ℝ) (source : ℝ → ℂ) (x : ℝ) :
    (Real.exp (shift / 2) : ℂ) *
        (((|Real.exp shift * x| : ℝ) : ℂ)⁻¹ * source (Real.exp shift * x)⁻¹) =
      (Real.exp (-shift / 2) : ℂ) * (((|x| : ℝ) : ℂ)⁻¹) *
        source (Real.exp (-shift) * x⁻¹) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos shift)]
  simp only [Complex.ofReal_mul, mul_inv_rev]
  rw [← Real.exp_neg]
  rw [show (Real.exp shift : ℂ)⁻¹ = (Real.exp (-shift) : ℂ) by
    simp only [Real.exp_neg, Complex.ofReal_inv]]
  have weight : (Real.exp (shift / 2) : ℂ) * (Real.exp (-shift) : ℂ) =
      Real.exp (-shift / 2) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  change (Real.exp (shift / 2) : ℂ) *
      ((((|x| : ℝ) : ℂ)⁻¹) * (Real.exp (-shift) : ℂ) *
        source (x⁻¹ * Real.exp (-shift))) = _
  rw [mul_comm x⁻¹ (Real.exp (-shift))]
  calc
    _ = ((Real.exp (shift / 2) : ℂ) * (Real.exp (-shift) : ℂ)) *
        (((|x| : ℝ) : ℂ)⁻¹) * source (Real.exp (-shift) * x⁻¹) := by ring
    _ = _ := by rw [weight]

/-- The same observation band reads the reciprocal outer source shell. -/
theorem burnolSourceReciprocal_shell (shift x : ℝ) (nonzero : x ≠ 0) :
    (q * Real.exp (-shift) ≤ |x| ∧ |x| ≤ q) ↔
      (4 * Real.exp (-shift) ≤ |Real.exp (-shift) * x⁻¹| ∧
        |Real.exp (-shift) * x⁻¹| ≤ 4) := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have scalePositive := Real.exp_pos (-shift)
  rw [abs_mul, abs_of_pos scalePositive, abs_inv, ← div_eq_mul_inv,
    le_div_iff₀ positive, div_le_iff₀ positive]
  constructor
  · rintro ⟨lower, upper⟩
    constructor <;> nlinarith
  · rintro ⟨lower, upper⟩
    constructor <;> nlinarith

/-- The second forcing is the actual L² Tate action of the same source,
with its reciprocal Jacobian visible before the mean-zero projection. -/
theorem burnolMobiusSourceL2_reciprocal_dilation_raw (shift : ℝ) (value : Ambient) :
    (burnolMultiplicativeDilation shift
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 value)) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp (-shift / 2) : ℂ) * (((|x| : ℝ) : ℂ)⁻¹) *
        burnolMobiusSourceL2 value (Real.exp (-shift) * x⁻¹) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  filter_upwards [burnolMultiplicativeDilation_coeFn shift
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 value)),
    qmp.ae (burnolTateReciprocalL2_coeFn (burnolMobiusSourceL2 value))]
      with x hmove hsource
  rw [hmove]
  unfold burnolL2RawNormalizedDilation
  rw [hsource]
  exact burnolSourceReciprocal_dilation_raw shift (burnolMobiusSourceL2 value) x

theorem burnolMobiusSourceL2_reciprocal_quarter_raw (shift : ℝ) (value : Ambient) :
    (burnolQuarterRestriction (burnolMultiplicativeDilation shift
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 value))) : ℝ → ℂ) =ᵐ[
        volume.restrict (symmetricInterval q)]
      fun x => (Real.exp (-shift / 2) : ℂ) * (((|x| : ℝ) : ℂ)⁻¹) *
        burnolMobiusSourceL2 value (Real.exp (-shift) * x⁻¹) := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolMultiplicativeDilation shift
        (burnolTateReciprocalL2 (burnolMobiusSourceL2 value))),
    ae_restrict_of_ae (s := symmetricInterval q)
      (burnolMobiusSourceL2_reciprocal_dilation_raw shift value)]
        with x hread hsource
  exact hread.trans hsource

/-- The original Fourier slot reads the same source's reciprocal outer
shell, through the actual Pa source law rather than an extra evaluation. -/
theorem burnolPaFourierForcing_quarter_raw (shift : ℝ) (value : Ambient)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    (burnolQuarterRestriction (burnolMultiplicativeDilation shift
      (burnolMobiusSourceL2 (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value))) :
        ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)]
      fun x => (Real.exp (-shift / 2) : ℂ) * (((|x| : ℝ) : ℂ)⁻¹) *
        burnolMobiusSourceL2 value (Real.exp (-shift) * x⁻¹) := by
  have sourceFourier : burnolMobiusSourceL2
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) =
        burnolTateReciprocalL2 (burnolMobiusSourceL2 value) :=
    burnolMobiusSource_fourier value inPa
  rw [sourceFourier]
  exact burnolMobiusSourceL2_reciprocal_quarter_raw shift value

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
