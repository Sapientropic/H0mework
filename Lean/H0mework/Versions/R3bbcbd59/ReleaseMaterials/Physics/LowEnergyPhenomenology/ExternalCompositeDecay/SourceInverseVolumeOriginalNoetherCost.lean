import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeScalarSignedInverseReturn
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherCurrentSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseOriginalNoetherCost
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy SourceScalarInverseRetardedBudget
open SourceScalarSignedInverseReturn SourceInverseFormSpectral SourceInverseNoetherCurrentSpectral
open SourceInverseNeutralRemainderClosed SourceInverseCoframeJointTailReturn SourceJointResidualEnergy
open SourceFourPoleEnergyClosed FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ENNReal
attribute [local irreducible] state inverseForm closedCurrent closedInverseMoment closedRemainderCost closedJointCost

/-- The original complete cost reads the exact same localized form integrated by the spectral producer. -/
theorem actual_localized_cost_closed (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    localizedInverseCost m ell F μ hμ g k=
      ENNReal.ofReal (closedInverseMoment F μ g k 1 (theta m ell)) := by
  have hs (z : ℂ) (hz : z.im≠0) (x : diagonal.domain) :
      embed (state F z hz x)=finiteResolvent F z (x : H) := by
    unfold state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simpa only [localizedInverseCost,normInverseMoment,Module.End.one_apply,hs,
    SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial] using
    actual_inverse_moment_lintegral F μ hμ g k 1 (theta m ell)

private theorem price_nonnegative (sharp : Bool) : 0 ≤ formPrice sharp := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  unfold formPrice coefficientCost
  positivity

/-- All paid source errors enter one common event; the only retained price is the original signed Noether integral. -/
theorem actual_remainder_signed_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter : Filter Index),
      closedRemainderCost sharp m ell F μ g k ≤
        ε+(2*formPrice sharp/μ)*closedCurrent F μ g k 1 (theta m ell) := by
  intro ε hε
  let C := formPrice sharp
  have hC : 0 ≤ C := price_nonnegative sharp
  let δ := ε/(2*(C+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N₁,h₁⟩ := actual_closed_inverse_budget sharp μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_localized_signed_budget μ hμ g k δ hδ
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hell] with F hF
  rw [actual_localized_cost_closed,←ENNReal.ofReal_mul hC,
    ←ENNReal.ofReal_add (by positivity : 0 ≤ ε/2)
      (mul_nonneg hC (actual_inverse_moment_nonnegative F μ hμ g k 1 (theta m ell)))] at hF
  have hR := (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (by positivity) (mul_nonneg hC
      (actual_inverse_moment_nonnegative F μ hμ g k 1 (theta m ell))))).mp hF
  have hJ := mul_le_mul_of_nonneg_left
    (h₂ m ((le_max_right _ _).trans hm) ell hell F) hC
  have hd : δ*(2*(C+1))=ε := by dsimp [δ];exact div_mul_cancel₀ _ (by positivity)
  have hCd : C*δ ≤ ε/2 := by nlinarith
  change closedRemainderCost sharp m ell F μ g k ≤ ε+(2*C/μ)*closedCurrent F μ g k 1 (theta m ell)
  calc
    _ ≤ ε/2+C*(δ+(2/μ)*closedCurrent F μ g k 1 (theta m ell)) := hR.trans (add_le_add le_rfl hJ)
    _ ≤ ε+(2*C/μ)*closedCurrent F μ g k 1 (theta m ell) := by
      simp only [div_eq_mul_inv] at hCd ⊢
      nlinarith only [hCd]

private theorem joint_energy_upper (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ENNReal.ofReal (closedJointCost sharp m ell F μ (g : H) (k : H)) ≤
      ENNReal.ofReal 2*ENNReal.ofReal (closedRemainderCost sharp m ell F μ g k)+
      ENNReal.ofReal 2*(∫⁻ w : ℝ,ENNReal.ofReal (‖jointResidual sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k-coframeJointProfile sharp m ell F g k (line μ w)‖^2)) := by
  rw [←actual_joint_closed_lintegral sharp m ell F μ hμ g k,←actual_profile_closed_lintegral sharp m ell F μ hμ g k]
  have hq := (actual_profile_integrable sharp m ell F μ hμ g k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal 2*ENNReal.ofReal (‖coframeJointProfile sharp m ell F g k (line μ w)‖^2)+
        ENNReal.ofReal 2*ENNReal.ofReal (‖jointResidual sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k-coframeJointProfile sharp m ell F g k (line μ w)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (by norm_num),←ENNReal.ofReal_mul (by norm_num),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h := norm_add_le (jointResidual sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k-coframeJointProfile sharp m ell F g k (line μ w))
        (coframeJointProfile sharp m ell F g k (line μ w))
      rw [sub_add_cancel] at h
      nlinarith [sq_nonneg (‖jointResidual sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k-coframeJointProfile sharp m ell F g k (line μ w)‖-
        ‖coframeJointProfile sharp m ell F g k (line μ w)‖),
        norm_nonneg (jointResidual sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k)]
    _ = _ := by
      rw [lintegral_add_left' (hq.const_mul (ENNReal.ofReal 2)),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The original whole signed joint cost directly consumes the source Noether integral on one common cutoff/cofinal event. -/
theorem actual_original_signed_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter : Filter Index),
      closedJointCost sharp m ell F μ (g : H) (k : H) ≤
        ε+(4*formPrice sharp/μ)*closedCurrent F μ g k 1 (theta m ell) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := actual_remainder_signed_budget sharp μ hμ g k (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_joint_coframe_difference_tail sharp μ hμ g k (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hell,
    h₂ m ((le_max_right _ _).trans hm) ell hell] with F hF₁ hF₂
  have hE := (joint_energy_upper sharp m ell F μ hμ g k).trans
    (add_le_add le_rfl (mul_le_mul' (le_refl (ENNReal.ofReal 2)) hF₂))
  rw [←ENNReal.ofReal_mul (by norm_num),←ENNReal.ofReal_mul (by norm_num),
    ←ENNReal.ofReal_add (mul_nonneg (by norm_num) (actual_closed_nonneg sharp m ell F μ hμ g k))
      (by positivity : 0 ≤ 2*(ε/4))] at hE
  have hR := (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (mul_nonneg (by norm_num) (actual_closed_nonneg sharp m ell F μ hμ g k)) (by positivity))).mp hE
  simp only [div_eq_mul_inv] at hR hF₁ ⊢
  nlinarith only [hR,hF₁]

end LowEnergy.SourceInverseOriginalNoetherCost
