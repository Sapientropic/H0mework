import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.TailRate

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong

open Complex Filter MeasureTheory Set
open scoped Topology

open private channelSlope channel_derivative channel_continuous cell from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong

local notation "C" => ContinuousChannels.channel

private def channelScale (d k : ℝ) : BurnolL2 →L[ℝ] BurnolL2 :=
  (((Real.sqrt k : ℂ)⁻¹) •
    (burnolMultiplicativeDilation (d*Real.log k)).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ

private theorem channel_scale_apply (d k : ℝ) (v : BurnolL2) :
    channelScale d k v = C d k v := rfl

private theorem channel_scale_norm (d k : ℝ) (v : BurnolL2) :
    ‖channelScale d k v‖ = (Real.sqrt k)⁻¹*‖v‖ := by
  rw [channel_scale_apply, ContinuousChannels.channel, norm_smul, LinearIsometryEquiv.norm_map,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

private theorem channel_one (d : ℝ) (v : BurnolL2) : C d 1 v = v := by
  simp only [ContinuousChannels.channel, Real.sqrt_one, Complex.ofReal_one, inv_one, Real.log_one,
    mul_zero, burnolMultiplicativeDilation_zero, one_smul]

private theorem channel_mul_scale (d k t : ℝ) (hk : 0 < k) (ht : 0 < t) (v : BurnolL2) :
    C d (k*t) v = channelScale d k (C d t v) := by
  rw [channel_scale_apply]
  simp only [ContinuousChannels.channel, Real.sqrt_mul hk.le, Complex.ofReal_mul,
    mul_inv_rev, Real.log_mul hk.ne' ht.ne', mul_add, burnolMultiplicativeDilation_add,
    map_smul, smul_smul]
  rw [mul_comm]

private def endpointRemainder (d : ℝ) (v : BurnolL2) (n : Nat) : BurnolL2 :=
  cell d v n-(1/2 : ℝ) • (C d ((n : ℝ)+1) v-C d ((n : ℝ)+2) v)

private theorem affine_cell_bound (f : ℝ → BurnolL2) (z w : BurnolL2)
    (regular : IntervalIntegrable f volume 0 1) (e : ℝ) (nonnegative : 0 ≤ e)
    (error : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t-(z+t • w)‖ ≤ e) :
    ‖z-(∫ t : ℝ in 0..1, f t)-(1/2 : ℝ) • (z-f 1)‖ ≤ 2*e := by
  let r := fun t : ℝ => f t-(z+t • w)
  have line : IntervalIntegrable (fun t : ℝ => z+t • w) volume 0 1 :=
    (continuous_const.add (continuous_id.smul continuous_const)).intervalIntegrable 0 1
  have price : (∫ t : ℝ in 0..1, z+t • w) = z+(1/2 : ℝ) • w := by
    have slope : IntervalIntegrable (fun t : ℝ => t • w) volume 0 1 :=
      (continuous_id.smul continuous_const).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => z) (g := fun t : ℝ => t • w)
      intervalIntegrable_const slope, intervalIntegral.integral_const,
      intervalIntegral.integral_smul_const (f := fun x : ℝ => x), integral_id]
    norm_num
  have integrated : (∫ t : ℝ in 0..1, r t) = (∫ t : ℝ in 0..1, f t)-(z+(1/2 : ℝ) • w) := by
    rw [intervalIntegral.integral_sub regular line, price]
  have residual : z-(∫ t : ℝ in 0..1, f t)-(1/2 : ℝ) • (z-f 1) =
      (1/2 : ℝ) • r 1-(∫ t : ℝ in 0..1, r t) := by
    rw [integrated]
    simp only [r, one_smul]
    module
  have integralBound : ‖∫ t : ℝ in 0..1, r t‖ ≤ e := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => error t (Ioc_subset_Icc_self (by
        simpa only [uIoc_of_le zero_le_one] using ht)))).trans_eq
    norm_num
  rw [residual]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have endBound := error 1 ⟨zero_le_one, le_rfl⟩
  linarith

/-- Removing the endpoint difference leaves a uniformly smaller tail of the original cells. -/
private theorem endpoint_cell_eventually (d : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0)
    (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ‖endpointRemainder d state n‖ ≤
      (2*ε)*((n : ℝ)+1)^(-(3/2 : ℝ)) := by
  let V := d • velocity-(1/2 : ℝ) • state
  have deriv : HasDerivAt (fun a : ℝ => C d a state) V 1 := by
    simpa only [V, channelSlope, Real.one_rpow, Real.log_one, mul_zero,
      burnolMultiplicativeDilation_zero, one_smul] using
      channel_derivative d state velocity source (a := 1) zero_lt_one
  obtain ⟨δ, δpos, close⟩ := Metric.mem_nhds_iff.mp (deriv.isLittleO.def positive)
  have indices : Tendsto (fun n : Nat => (n : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  filter_upwards [(tendsto_inv_atTop_zero.comp indices).eventually (eventually_lt_nhds δpos)]
    with n narrow
  let k : ℝ := (n : ℝ)+1
  let f := fun u : ℝ => C d (k+u) state
  let w := k⁻¹ • channelScale d k V
  have kp : 0 < k := by dsimp [k]; positivity
  have regular : IntervalIntegrable f volume 0 1 :=
    (((channel_continuous d state velocity source).comp
      (continuous_const.add continuous_id).continuousOn)
      (by intro u inside; exact add_pos_of_pos_of_nonneg kp inside.1)).intervalIntegrable_of_Icc zero_le_one
  have localBound (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) :
      ‖f u-(C d k state+u • w)‖ ≤ ε*k^(-(3/2 : ℝ)) := by
    have nonnegative : 0 ≤ u/k := div_nonneg inside.1 kp.le
    have near : u/k ≤ k⁻¹ := by simpa only [one_div] using
      (div_le_div_of_nonneg_right inside.2 kp.le)
    have ball : 1+u/k ∈ Metric.ball (1 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_nonneg nonnegative]
      exact near.trans_lt narrow
    have small := close ball
    change ‖C d (1+u/k) state-C d 1 state-(1+u/k-1) • V‖ ≤ ε*‖1+u/k-1‖ at small
    rw [channel_one, add_sub_cancel_left, Real.norm_of_nonneg nonnegative] at small
    have relative : k+u = k*(1+u/k) := by field_simp [kp.ne']
    have equation : f u-(C d k state+u • w) =
        channelScale d k (C d (1+u/k) state-state-(u/k) • V) := by
      dsimp only [f, w]
      rw [relative, channel_mul_scale d k _ kp (by positivity), ← channel_scale_apply d k state]
      simp only [map_sub, map_smul, sub_add_eq_sub_sub, smul_smul, div_eq_mul_inv]
    rw [equation, channel_scale_norm]
    apply (mul_le_mul_of_nonneg_left (small.trans (mul_le_mul_of_nonneg_left near positive.le))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg kp.le, ← Real.rpow_neg_one,
      mul_left_comm, ← Real.rpow_add kp]
    norm_num
  have shift : (∫ a : ℝ in k..k+1, C d a state) = ∫ u : ℝ in 0..1, f u := by
    simpa only [f, zero_add, add_comm] using
      (intervalIntegral.integral_comp_add_left (f := fun a : ℝ => C d a state) k
        (a := (0 : ℝ)) (b := 1)).symm
  have next : (n : ℝ)+2=k+1 := by dsimp [k]; ring
  unfold endpointRemainder cell
  change ‖C d k state-(∫ a : ℝ in k..(n : ℝ)+2, C d a state)-
    (1/2 : ℝ) • (C d k state-C d ((n : ℝ)+2) state)‖ ≤ _
  rw [next, shift]
  exact (affine_cell_bound f _ w regular _ (mul_nonneg positive.le (Real.rpow_nonneg kp.le _))
    localBound).trans_eq (by change 2*(ε*k^(-(3/2 : ℝ))) = (2*ε)*k^(-(3/2 : ℝ)); ring)

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
