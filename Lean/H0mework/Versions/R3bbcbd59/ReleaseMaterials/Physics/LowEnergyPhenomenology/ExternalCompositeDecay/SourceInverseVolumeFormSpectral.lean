import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherEnergy
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeElectricMomentGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseFormSpectral
open GaussFockPair GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy SourceInverseNoetherEnergy
open SourceInverseElectricMomentGram SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] inverseForm bulkAction state productMoment closedMomentGram

/-- Real polarization is applied to the original inverse Ward form on the same core. -/
theorem original_inverse_polarization (f : QuantumTest) :
    inverseForm f=(‖embed (f+bulkAction f)‖^2-‖embed (f-bulkAction f)‖^2)/4 := by
  rw [←original_bulk_energy]
  unfold sourcePair
  simpa only [map_add,map_sub,pow_two] using!
    re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ) (embed f) (embed (bulkAction f))

def normInverseMoment (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) (w : ℝ) : ℝ :=
  ‖embed (A (state F (star (line μ w))
    (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne') k))‖^2 *
    inverseForm (B (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))

/-- Both signed Grams retain all original channels, including escape and interference. -/
def closedInverseMoment (F : Index) (μ : ℝ) (g k : diagonal.domain) (A B : End) : ℝ :=
  (closedMomentGram F μ g k A (B+bulkAction*B)-
    closedMomentGram F μ g k A (B-bulkAction*B))/4

private theorem actual_moment_polarization (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain)
    (A B : End) (w : ℝ) :
    normInverseMoment F μ hμ g k A B w=
      (productMoment F μ hμ g k A (B+bulkAction*B) w-
        productMoment F μ hμ g k A (B-bulkAction*B) w)/4 := by
  unfold normInverseMoment productMoment
  rw [original_inverse_polarization]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply]
  ring

/-- The actual moving inverse form has a finite full-frequency moment at each original F. -/
theorem actual_inverse_moment_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    Integrable (normInverseMoment F μ hμ g k A B) := by
  have hi := ((actual_product_integrable F μ hμ g k A (B+bulkAction*B)).sub
    (actual_product_integrable F μ hμ g k A (B-bulkAction*B))).div_const 4
  exact hi.congr (Filter.Eventually.of_forall (fun w => (actual_moment_polarization F μ hμ g k A B w).symm))

/-- The four-pole closed kernel integrates the unaltered local source form, not a reader norm majorant. -/
theorem actual_inverse_moment_closed (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    (∫ w : ℝ,normInverseMoment F μ hμ g k A B w)=closedInverseMoment F μ g k A B := by
  simp_rw [actual_moment_polarization]
  rw [integral_div,integral_sub (actual_product_integrable F μ hμ g k A (B+bulkAction*B))
    (actual_product_integrable F μ hμ g k A (B-bulkAction*B)),actual_product_gram,actual_product_gram]
  rfl

theorem actual_inverse_moment_nonnegative (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    0 ≤ closedInverseMoment F μ g k A B := by
  rw [←actual_inverse_moment_closed F μ hμ g k A B]
  exact integral_nonneg (fun w => mul_nonneg (sq_nonneg _) (original_inverse_nonnegative _))

theorem actual_inverse_moment_lintegral (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    (∫⁻ w : ℝ,ENNReal.ofReal (normInverseMoment F μ hμ g k A B w))=
      ENNReal.ofReal (closedInverseMoment F μ g k A B) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (actual_inverse_moment_integrable F μ hμ g k A B)
    (Filter.Eventually.of_forall (fun w => mul_nonneg (sq_nonneg _) (original_inverse_nonnegative _))),
    actual_inverse_moment_closed]

end LowEnergy.SourceInverseFormSpectral
