import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceBulkParseval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceBulkTimeEnergyBudget
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceBulkParseval SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy SourceScalarInverseRetardedBudget
open SourceScalarSignedInverseReturn SourceInverseFormSpectral SourceInverseNoetherCurrentSpectral
open SourceInverseNeutralRemainderClosed SourceInverseCoframeJointTailReturn SourceJointResidualEnergy
open SourceInverseOriginalNoetherCost SourceFourPoleEnergyClosed FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
attribute [local irreducible] state inverseForm closedInverseMoment closedRemainderCost closedJointCost timeEnergy

private theorem price_nonnegative (sharp : Bool) : 0 ≤ formPrice sharp := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  unfold formPrice coefficientCost
  positivity

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

/-- The original whole cost is controlled by one positive time-energy source, with an F-independent external-leg price. -/
theorem actual_original_time_energy_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤
          ε+(4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2)*timeEnergy F μ (theta m ell) g := by
  intro ε hε
  have hp := price_nonnegative sharp
  obtain ⟨NI,hI⟩ := actual_closed_inverse_budget sharp μ hμ g k (ε/4) (by positivity)
  obtain ⟨ND,hD⟩ := actual_joint_coframe_difference_tail sharp μ hμ g k (ε/4) (by positivity)
  refine ⟨max NI ND,fun m hm ell hell => ?_⟩
  filter_upwards [hI m ((le_max_left _ _).trans hm) ell hell,
    hD m ((le_max_right _ _).trans hm) ell hell] with F hFI hFD
  rw [actual_localized_cost_closed] at hFI
  have hi := actual_inverse_moment_nonnegative F μ hμ g k 1 (theta m ell)
  rw [←ENNReal.ofReal_mul hp,←ENNReal.ofReal_add (by positivity : 0≤ε/4) (mul_nonneg hp hi)] at hFI
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤ε/4+formPrice sharp*closedInverseMoment F μ g k 1 (theta m ell))).mp hFI
  have hj := (joint_energy_upper sharp m ell F μ hμ g k).trans
    (add_le_add le_rfl (mul_le_mul' (le_refl (ENNReal.ofReal 2)) hFD))
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
    ←ENNReal.ofReal_add (mul_nonneg (by norm_num) (actual_closed_nonneg sharp m ell F μ hμ g k)) (by positivity : 0≤2*(ε/4))] at hj
  have hrc := actual_closed_nonneg sharp m ell F μ hμ g k
  have hjr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤2*closedRemainderCost sharp m ell F μ g k+2*(ε/4))).mp hj
  have ht := mul_le_mul_of_nonneg_left (actual_weighted_bulk_upper F μ hμ (theta m ell) g k) hp
  nlinarith only [hr,hjr,ht]

end LowEnergy.SourceBulkTimeEnergyBudget
