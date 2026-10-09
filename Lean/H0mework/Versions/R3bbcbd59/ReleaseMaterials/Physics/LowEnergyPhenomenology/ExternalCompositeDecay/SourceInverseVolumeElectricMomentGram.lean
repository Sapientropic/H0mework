import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeElectricMomentChannels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseElectricMomentGram
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceInverseElectricMomentChannels SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev GramIndex (F : Index) := Channel F × Channel F × Channel F × Channel F
attribute [local irreducible] state mappedChannel channelGram

def productMoment (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) (w : ℝ) : ℝ :=
  ‖embed (A (state F (star (line μ w))
      (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne') k))‖^2*
    ‖embed (B (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2

private def frequencyTerm (F : Index) (μ : ℝ) (g k : diagonal.domain) (A B : End)
    (r : GramIndex F) (w : ℝ) : ℂ :=
  (star (polePair μ (channelValue F r.2.1) (channelValue F r.2.2.1) w)*
    polePair μ (channelValue F r.1) (channelValue F r.2.2.2) w)*
      channelGram F g k A B r.1 r.2.1 r.2.2.1 r.2.2.2

def closedMomentGram (F : Index) (μ : ℝ) (g k : diagonal.domain) (A B : End) : ℝ :=
  (∑ r : GramIndex F,
    closedKernel μ (channelValue F r.2.1) (channelValue F r.2.2.1)
      (channelValue F r.1) (channelValue F r.2.2.2)*
        channelGram F g k A B r.1 r.2.1 r.2.2.1 r.2.2.2).re

private theorem pointwise (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) (w : ℝ) :
    productMoment F μ hμ g k A B w=(∑ r : GramIndex F,frequencyTerm F μ g k A B r w).re := by
  have h := congrArg Complex.re (actual_moment_channels F μ hμ w g k A B)
  simpa only [Complex.ofReal_re,Fintype.sum_prod_type,frequencyTerm,productMoment] using h

private theorem term_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End)
    (r : GramIndex F) : Integrable (frequencyTerm F μ g k A B r) :=
  (four_pole_integrable μ _ _ _ _ hμ).mul_const _

/-- The literal mixed two-leg product is integrable with every interference coefficient retained. -/
theorem actual_product_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    Integrable (productMoment F μ hμ g k A B) := by
  have hi := integrable_finsetSum Finset.univ (fun r _ => term_integrable F μ hμ g k A B r)
  exact hi.re.congr (Filter.Eventually.of_forall (fun w => (pointwise F μ hμ g k A B w).symm))

/-- The original four-pole kernel exactly integrates the actual source-mapped channel Gram. -/
theorem actual_product_gram (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    (∫ w : ℝ,productMoment F μ hμ g k A B w)=closedMomentGram F μ g k A B := by
  have hi (r : GramIndex F) := term_integrable F μ hμ g k A B r
  have ht (r : GramIndex F) : (∫ w : ℝ,frequencyTerm F μ g k A B r w)=
      closedKernel μ (channelValue F r.2.1) (channelValue F r.2.2.1)
        (channelValue F r.1) (channelValue F r.2.2.2)*
          channelGram F g k A B r.1 r.2.1 r.2.2.1 r.2.2.2 := by
    unfold frequencyTerm
    rw [integral_mul_const]
    exact congrArg (fun c : ℂ => c*channelGram F g k A B r.1 r.2.1 r.2.2.1 r.2.2.2)
      (four_pole_closed μ _ _ _ _ hμ)
  simp_rw [pointwise F μ hμ g k A B]
  change (∫ w : ℝ,RCLike.re (∑ r : GramIndex F,frequencyTerm F μ g k A B r w))=closedMomentGram F μ g k A B
  rw [integral_re (integrable_finsetSum Finset.univ (fun r _ => hi r)),
    integral_finsetSum Finset.univ (fun r _ => hi r)]
  simp_rw [ht]
  rfl

theorem actual_product_gram_nonneg (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    0 ≤ closedMomentGram F μ g k A B := by
  rw [←actual_product_gram F μ hμ g k A B]
  exact integral_nonneg (fun w => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem actual_product_gram_lintegral (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (A B : End) :
    (∫⁻ w : ℝ,ENNReal.ofReal (productMoment F μ hμ g k A B w))=ENNReal.ofReal (closedMomentGram F μ g k A B) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (actual_product_integrable F μ hμ g k A B)
    (Filter.Eventually.of_forall (fun w => mul_nonneg (sq_nonneg _) (sq_nonneg _))),actual_product_gram]

end LowEnergy.SourceInverseElectricMomentGram
