import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherEnergy
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarInverseEnergyExchange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseFixedEnergyTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourcePhysicalKineticSquare SourceScalarVirialBulk SourceScalarPositiveBulkWard
open SourceScalarInverseBulk SourceScalarInverseNativeEnergy SourceScalarInverseRetardedBudget
open SourceScalarInverseEnergyExchange SourceInverseNoetherEnergy InverseVolumeLocalizationAlgebra
open SourceRelativePowerTail SourceRetardedBandCurrent SourceHardyRetardedTail
open SourceQuantumScalarChart FullYSourceResolventGraphSplice

attribute [local irreducible] diagonalAction positiveBulk inverseVolumeAction inverseForm
  inverseWeightedBulkJet inverseSymmetricScale state sourcePair bulkAction inverseContact

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (theta m ell g)=sourcePair (theta m ell f) g :=
  multiply_pair _ _ _ _

private theorem square_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (square m ell g)=sourcePair (square m ell f) g := by
  change sourcePair f (theta m ell (theta m ell g))=sourcePair (theta m ell (theta m ell f)) g
  rw [theta_pair,theta_pair]

private theorem jordan_diagonal (m ell : ℕ) (f : QuantumTest) :
    (sourcePair f (jordan bulkAction (square m ell) f)).re=
      (sourcePair (square m ell f) (bulkAction f)).re := by
  simp only [jordan,LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply]
  have he : sourcePair f ((1/2 : ℂ) • (bulkAction (square m ell f)+square m ell (bulkAction f)))=
      (1/2 : ℂ)*(sourcePair f (bulkAction (square m ell f))+sourcePair f (square m ell (bulkAction f))) := by
    simp only [sourcePair,map_smul,map_add,inner_smul_right,inner_add_right]
  rw [he,original_bulk_pair f (square m ell f),square_pair m ell f (bulkAction f)]
  have hs : (sourcePair (bulkAction f) (square m ell f)).re=
      (sourcePair (square m ell f) (bulkAction f)).re := by
    unfold sourcePair
    exact inner_re_symm (𝕜 := ℂ) (embed (bulkAction f)) (embed (square m ell f))
  have hc (c : ℂ) : ((1/2 : ℂ)*c).re=(1/2 : ℝ)*c.re := by norm_num [Complex.mul_re]
  rw [hc,Complex.add_re,hs]
  ring

/-- The whole inverse Ward energy of the fixed cutoff input is its theta² endpoint plus actual native70 contact. -/
theorem original_fixed_energy_ims (m ell : ℕ) (f : QuantumTest) :
    inverseForm (theta m ell f)=
      (sourcePair (square m ell f) (bulkAction f)).re+(inverseContact m ell f f).re := by
  rw [inverseForm,original_inverse_bilinear_ims,Complex.add_re,←bulkAction,jordan_diagonal]

private theorem contact_inverse (v : GaussLiveMomentum.Ambient) (m ell : ℕ) (f : QuantumTest) :
    SourceNativeCutoffContact.contactAction v m ell (inverseVolumeAction f)=
      inverseVolumeAction (SourceNativeCutoffContact.contactAction v m ell f) := by
  unfold inverseVolumeAction
  apply DFunLike.ext
  intro z
  exact map_smul (SourceNativeCutoffContact.contactFiber v m ell z) (reciprocalVolume z : ℂ) (f z)

/-- The paid seventy-row bound is evaluated on V f; no new energy assumption or factor is introduced. -/
theorem original_fixed_contact_bound (m ell : ℕ) (hell : m ≤ ell) (f : QuantumTest) :
    (inverseContact m ell f f).re ≤
      (1120*sourceTime 0*‖embed (inverseVolumeAction f)‖^2)/(m+2 : ℝ)^2 := by
  have h := SourceScalarBulkResidualBudget.original_contact_pair_bound m ell hell
    (inverseVolumeAction f) (inverseVolumeAction f)
  have he : SourceScalarBulkResidualBudget.contactPair m ell (inverseVolumeAction f) (inverseVolumeAction f)=
      inverseContact m ell f f := by
    simp only [SourceScalarBulkResidualBudget.contactPair,SourceScalarBulkResidualBudget.C,
      contact_inverse,inverseContact]
  rw [he] at h
  exact (Complex.re_le_norm _).trans (h.trans_eq (by ring))

/-- Its only source data are f, Bf and Vf; the upper cutoff is uniform. -/
theorem original_fixed_energy_bound (m ell : ℕ) (hell : m ≤ ell) (f : QuantumTest) :
    inverseForm (theta m ell f) ≤
      ‖relativeTail m ell (embed f)‖*‖embed (bulkAction f)‖+
      (1120*sourceTime 0*‖embed (inverseVolumeAction f)‖^2)/(m+2 : ℝ)^2 := by
  rw [original_fixed_energy_ims]
  have hθ : ‖embed (square m ell f)‖ ≤ ‖relativeTail m ell (embed f)‖ := by
    change ‖embed (SourceNativeCutoffContact.thetaAction m ell
      (SourceNativeCutoffContact.thetaAction m ell f))‖ ≤ _
    rw [SourceNativeCutoffContact.theta_core,SourceNativeCutoffContact.theta_core]
    exact relative_tail_contraction m ell hell _
  have hi : ‖sourcePair (square m ell f) (bulkAction f)‖ ≤
      ‖embed (square m ell f)‖*‖embed (bulkAction f)‖ := by
    unfold sourcePair
    exact norm_inner_le_norm _ _
  have he := (Complex.re_le_norm (sourcePair (square m ell f) (bulkAction f))).trans
    (hi.trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _)))
  exact add_le_add he (original_fixed_contact_bound m ell hell f)

/-- The same fixed source has a common m/ell inverse-energy tail, generated from original theta² and native contacts. -/
theorem original_fixed_energy_tail (f : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      inverseForm (theta m ell f) ≤ ε := by
  intro ε hε
  let C := 1120*sourceTime 0*‖embed (inverseVolumeAction f)‖^2
  have hp : 0 < ‖embed (bulkAction f)‖+1 := by positivity
  obtain ⟨N₁,hN₁⟩ := original_relative_tail (embed f)
    ((ε/2)/(‖embed (bulkAction f)‖+1)) (div_pos (by linarith) hp)
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (C/(ε/2))
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  have hm₁ : N₁ ≤ m := (le_max_left _ _).trans hm
  have hm₂ : N₂ ≤ m := (le_max_right _ _).trans hm
  have ht := hN₁ m hm₁ ell hell
  have he : ‖relativeTail m ell (embed f)‖*‖embed (bulkAction f)‖ ≤ ε/2 := by
    have hs := mul_lt_mul_of_pos_right ht hp
    rw [div_mul_cancel₀ _ hp.ne'] at hs
    nlinarith [norm_nonneg (relativeTail m ell (embed f))]
  have hmR : (N₂ : ℝ) ≤ m := Nat.cast_le.mpr hm₂
  have hd : 0 < (m+2 : ℝ) := by positivity
  have hdiv : C/(ε/2) < (m+2 : ℝ) := by linarith
  have hc : C < (ε/2)*(m+2 : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ (by linarith : 0 < ε/2)).mp hdiv
  have hpow : (m+2 : ℝ) ≤ (m+2 : ℝ)^2 := by
    have hm0 := Nat.cast_nonneg (α := ℝ) m
    nlinarith
  have hb : C/(m+2 : ℝ)^2 ≤ ε/2 := (div_le_iff₀ (pow_pos hd 2)).mpr
    (hc.le.trans (mul_le_mul_of_nonneg_left hpow (by linarith)))
  have h := original_fixed_energy_bound m ell hell f
  change inverseForm (theta m ell f) ≤
    ‖relativeTail m ell (embed f)‖*‖embed (bulkAction f)‖+C/(m+2 : ℝ)^2 at h
  linarith

/-- The actual fixed input is now paid; the sole remaining term of this Noether inequality is its joined source current. -/
theorem actual_noether_paid_fixed_tail (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ F : Index,∀ z : ℂ,∀ hz : z.im ≠ 0,
      z.im^2*inverseForm (theta m ell (state F z hz g)) ≤
        ε+2*z.im*raisedNoetherCurrent F (theta m ell) (state F z hz g) := by
  intro ε hε
  obtain ⟨N,hN⟩ := original_fixed_energy_tail (coreEquiv.symm g) ε hε
  refine ⟨N,fun m hm ell hell F z hz => ?_⟩
  have h := actual_raised_energy_upper F z hz g (theta m ell)
  have ht := hN m hm ell hell
  linarith

end LowEnergy.SourceInverseFixedEnergyTail
