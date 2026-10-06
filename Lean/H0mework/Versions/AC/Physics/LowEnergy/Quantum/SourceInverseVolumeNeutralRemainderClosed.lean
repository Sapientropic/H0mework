import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralRemainderSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseNeutralRemainderClosed
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseCoframeSpectralReturn SourceInverseNeutralRemainderSpectral SourceInverseCoframeJointTailReturn
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarForceBudget SourceResolventBandLimit
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
attribute [local irreducible] remainderCoefficient coframeJointProfile

def normalizedCoefficient (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) : Coeff F :=
  (oscillatorMass : ℂ)⁻¹ • remainderCoefficient sharp m ell F g (coreEquiv.symm g) (coreEquiv.symm k)

def closedRemainderCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g k : diagonal.domain) : ℝ :=
  (∑ ij : Channel F × Channel F,∑ kl : Channel F × Channel F,
    closedKernel μ (channelValue F ij.1) (channelValue F ij.2) (channelValue F kl.1) (channelValue F kl.2)*
      inner ℂ (normalizedCoefficient sharp m ell F g k ij) (normalizedCoefficient sharp m ell F g k kl)).re

/-- The original mass and original source seed normalize the complete signed spectral coefficient. -/
theorem actual_profile_decode (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) (w : ℝ) :
    coframeJointProfile sharp m ell F g k (line μ w)=decode F μ w (normalizedCoefficient sharp m ell F g k) := by
  have h := actual_remainder_decode sharp m ell F g (coreEquiv.symm g) (coreEquiv.symm k) μ hμ w
  have he (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply x)
  simp only [he] at h
  unfold coframeJointProfile normalizedCoefficient
  rw [h,map_smul,smul_eq_mul]

/-- The complete remainder is integrable after the original signed terms are combined. -/
theorem actual_profile_integrable (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) : Integrable (fun w : ℝ => ‖coframeJointProfile sharp m ell F g k (line μ w)‖^2) := by
  simp_rw [actual_profile_decode sharp m ell F μ hμ g k]
  change Integrable (fun w : ℝ => ‖∑ ij : Channel F × Channel F,
    polePair μ (channelValue F ij.1) (channelValue F ij.2) w • normalizedCoefficient sharp m ell F g k ij‖^2)
  exact finite_gram_integrable μ hμ _ _ _

/-- All source, H/d_F and correction cross terms enter the same original four-pole kernel. -/
theorem actual_profile_closed_energy (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    (∫ w : ℝ,‖coframeJointProfile sharp m ell F g k (line μ w)‖^2)=closedRemainderCost sharp m ell F μ g k := by
  simp_rw [actual_profile_decode sharp m ell F μ hμ g k]
  change (∫ w : ℝ,‖∑ ij : Channel F × Channel F,
    polePair μ (channelValue F ij.1) (channelValue F ij.2) w • normalizedCoefficient sharp m ell F g k ij‖^2)=_
  rw [finite_gram_integral μ hμ]
  simp_rw [four_pole_closed μ _ _ _ _ hμ]
  rfl

theorem actual_profile_closed_lintegral (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖coframeJointProfile sharp m ell F g k (line μ w)‖^2))=
      ENNReal.ofReal (closedRemainderCost sharp m ell F μ g k) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (actual_profile_integrable sharp m ell F μ hμ g k)
    (Filter.Eventually.of_forall (fun w => sq_nonneg _)),actual_profile_closed_energy sharp m ell F μ hμ g k]

theorem actual_closed_nonneg (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    0 ≤ closedRemainderCost sharp m ell F μ g k := by
  rw [←actual_profile_closed_energy sharp m ell F μ hμ g k]
  exact integral_nonneg (fun w => sq_nonneg _)

/-- The original cost consumer now reads this complete signed finite Gram without changing the common cutoff/F quantifiers. -/
theorem actual_original_tail_iff (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε) ↔
    (∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),closedRemainderCost sharp m ell F μ g k ≤ ε) := by
  rw [actual_joint_coframe_tail_iff sharp μ hμ g k]
  constructor <;> intro h ε hε
  · obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N,fun m hm ell hell => ?_⟩
    filter_upwards [hN m hm ell hell] with F hF
    rw [actual_profile_closed_lintegral sharp m ell F μ hμ g k] at hF
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hF
  · obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N,fun m hm ell hell => ?_⟩
    filter_upwards [hN m hm ell hell] with F hF
    rw [actual_profile_closed_lintegral sharp m ell F μ hμ g k]
    exact ENNReal.ofReal_le_ofReal hF

end LowEnergy.SourceInverseNeutralRemainderClosed
