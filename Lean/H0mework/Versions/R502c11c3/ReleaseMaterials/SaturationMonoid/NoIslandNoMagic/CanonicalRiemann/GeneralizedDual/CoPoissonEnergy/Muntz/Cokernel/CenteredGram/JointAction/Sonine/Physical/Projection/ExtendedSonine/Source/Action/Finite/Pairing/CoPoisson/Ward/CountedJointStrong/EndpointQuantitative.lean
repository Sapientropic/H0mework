import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointLimit

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong

open Filter MeasureTheory Set
open scoped Topology

open private channelSlope channel_derivative channel_continuous cell sourceValue source_tendsto from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong
open private endpointRemainder affine_cell_bound channel_one channelScale channel_scale_apply channel_scale_norm channel_mul_scale from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointCell
open private endpoint_prefix endpoint_channel_zero from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointLimit

local notation "D" => burnolMultiplicativeDilation
local notation "C" => ContinuousChannels.channel
local notation "finite" => fun d (v : BurnolL2) (N : Nat) =>
  (∑ n ∈ Finset.Ico 1 N, C d (n : ℝ) v) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), C d a v

private theorem inverse_scale_difference (t : ℝ) (ordered : 1 ≤ t) :
    |t^(-(3/2 : ℝ))-1| ≤ (3/2)*(t-1) := by
  have deriv (x : ℝ) (above : 1 ≤ x) :
      HasDerivAt (fun z : ℝ => z^(-(3/2 : ℝ))) (-(3/2 : ℝ)*x^(-(5/2 : ℝ))) x := by
    simpa only [show -(3/2 : ℝ)-1 = -(5/2 : ℝ) by norm_num] using
      (Real.hasDerivAt_rpow_const (p := -(3/2 : ℝ)) (Or.inl (by linarith : x ≠ 0)))
  have derivativeBound (x : ℝ) (above : 1 ≤ x) :
      ‖-(3/2 : ℝ)*x^(-(5/2 : ℝ))‖ ≤ 3/2 := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    norm_num
    linarith [Real.rpow_le_one_of_one_le_of_nonpos above (by norm_num : -(5/2 : ℝ) ≤ 0)]
  simpa only [Real.one_rpow, Real.norm_eq_abs] using
    (norm_image_sub_le_of_norm_deriv_le_segment' (a := (1 : ℝ)) (b := t)
      (fun x hx => (deriv x hx.1).hasDerivWithinAt) (fun x hx => derivativeBound x hx.1) t
      ⟨ordered, le_rfl⟩)

private theorem unit_slope_difference (d : ℝ) (state velocity : BurnolL2)
    (B : ℝ) (budget : 0 ≤ B)
    (move : ∀ h ∈ Icc (0 : ℝ) 1,
      ‖D (d*h) (d • velocity-(1/2 : ℝ) • state)-(d • velocity-(1/2 : ℝ) • state)‖ ≤ B*Real.sqrt h)
    (t : ℝ) (within : t ∈ Icc (1 : ℝ) 2) :
    ‖channelSlope d t state velocity-(d • velocity-(1/2 : ℝ) • state)‖ ≤
      (B+(3/2)*‖d • velocity-(1/2 : ℝ) • state‖)*Real.sqrt (t-1) := by
  let v := d • velocity-(1/2 : ℝ) • state
  let a := t^(-(3/2 : ℝ))
  have tp : 0 < t := zero_lt_one.trans_le within.1
  have h₀ := Real.log_nonneg within.1
  have h₁ := Real.log_le_sub_one_of_pos tp
  have small := move (Real.log t) ⟨h₀, h₁.trans (by linarith [within.2])⟩
  have a₀ : 0 ≤ a := Real.rpow_nonneg tp.le _
  have a₁ : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos within.1 (by norm_num)
  have d₀ : 0 ≤ t-1 := sub_nonneg.mpr within.1
  have root : t-1 ≤ Real.sqrt (t-1) := by
    have bound := Real.sqrt_le_sqrt (show t-1 ≤ 1 by linarith [within.2])
    rw [Real.sqrt_one] at bound
    nlinarith [Real.sq_sqrt d₀, Real.sqrt_nonneg (t-1)]
  have split : channelSlope d t state velocity-v = a • (D (d*Real.log t) v-v)+(a-1) • v := by
    dsimp only [channelSlope, a, v]
    module
  rw [split]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg a₀, Real.norm_eq_abs]
  change a*‖D (d*Real.log t) v-v‖+|a-1| *‖v‖ ≤ _
  have first : a*‖D (d*Real.log t) v-v‖ ≤ B*Real.sqrt (t-1) :=
    (mul_le_of_le_one_left (norm_nonneg _) a₁).trans
      (small.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h₁) budget))
  have second : |a-1| *‖v‖ ≤ ((3/2)*‖v‖)*Real.sqrt (t-1) := by
    calc
      _ ≤ ((3/2)*(t-1))*‖v‖ :=
        mul_le_mul_of_nonneg_right (inverse_scale_difference t within.1) (norm_nonneg _)
      _ = ((3/2)*‖v‖)*(t-1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left root (by positivity)
  exact (add_le_add first second).trans_eq (by ring)

private theorem endpoint_cell_rate (d : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => D h state) velocity 0)
    (B : ℝ) (budget : 0 ≤ B)
    (move : ∀ h ∈ Icc (0 : ℝ) 1,
      ‖D (d*h) (d • velocity-(1/2 : ℝ) • state)-(d • velocity-(1/2 : ℝ) • state)‖ ≤ B*Real.sqrt h)
    (n : Nat) :
    ‖endpointRemainder d state n‖ ≤
      (2*(B+(3/2)*‖d • velocity-(1/2 : ℝ) • state‖))/(((n : ℝ)+1)^2) := by
  let v := d • velocity-(1/2 : ℝ) • state
  let cost := B+(3/2)*‖v‖
  let k : ℝ := (n : ℝ)+1
  let f := fun u : ℝ => C d (k+u) state
  let w := k⁻¹ • channelScale d k v
  have cost₀ : 0 ≤ cost := add_nonneg budget (by positivity)
  have kp : 0 < k := by dsimp [k]; positivity
  have k₁ : 1 ≤ k := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have i₁ : k⁻¹ ≤ 1 := inv_le_one_of_one_le₀ k₁
  have regular : IntervalIntegrable f volume 0 1 :=
    (((channel_continuous d state velocity source).comp
      (continuous_const.add continuous_id).continuousOn)
      (by intro u inside; exact add_pos_of_pos_of_nonneg kp inside.1)).intervalIntegrable_of_Icc zero_le_one
  have lineError (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) :
      ‖f u-(C d k state+u • w)‖ ≤ cost/k^2 := by
    have near₀ : 0 ≤ u/k := div_nonneg inside.1 kp.le
    have near₁ : u/k ≤ k⁻¹ := by
      simpa only [one_div] using div_le_div_of_nonneg_right inside.2 kp.le
    let g := fun t : ℝ => C d t state-(state+(t-1) • v)
    have start : g 1 = 0 := by simp only [g, channel_one, sub_self, zero_smul, add_zero]
    have deriv (t : ℝ) (ht : t ∈ Icc (1 : ℝ) (1+k⁻¹)) :
        HasDerivWithinAt g (channelSlope d t state velocity-v) (Icc (1 : ℝ) (1+k⁻¹)) t := by
      have line := (hasDerivAt_const t state).add (((hasDerivAt_id t).sub_const 1).smul_const v)
      simpa only [g, Pi.sub_apply, Pi.add_apply, zero_add, one_smul, id_eq] using!
        ((channel_derivative d state velocity source (zero_lt_one.trans_le ht.1)).sub line).hasDerivWithinAt
    have bounded (t : ℝ) (ht : t ∈ Ico (1 : ℝ) (1+k⁻¹)) :
        ‖channelSlope d t state velocity-v‖ ≤ cost*Real.sqrt k⁻¹ :=
      (unit_slope_difference d state velocity B budget move t ⟨ht.1, by linarith [ht.2]⟩).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [ht.2])) cost₀)
    have localBound := norm_image_sub_le_of_norm_deriv_le_segment' deriv bounded (1+u/k)
      ⟨by linarith, by linarith⟩
    rw [start, sub_zero, add_sub_cancel_left] at localBound
    have relative : k+u = k*(1+u/k) := by field_simp [kp.ne']
    have equation : f u-(C d k state+u • w) = channelScale d k (g (1+u/k)) := by
      dsimp only [f, w, g]
      rw [relative, channel_mul_scale d k _ kp (by positivity), ← channel_scale_apply d k state]
      simp only [add_sub_cancel_left, map_sub, map_add, map_smul, smul_smul, div_eq_mul_inv]
    rw [equation, channel_scale_norm]
    refine (mul_le_mul_of_nonneg_left
      (localBound.trans (mul_le_mul_of_nonneg_left near₁ (by positivity))) (by positivity)).trans_eq ?_
    have rootSquare : (Real.sqrt k)⁻¹*(Real.sqrt k)⁻¹ = k⁻¹ := by
      rw [← pow_two, inv_pow, Real.sq_sqrt kp.le]
    rw [Real.sqrt_inv, div_eq_mul_inv, ← inv_pow]
    calc
      _ = cost*((Real.sqrt k)⁻¹*(Real.sqrt k)⁻¹)*k⁻¹ := by ring
      _ = _ := by rw [rootSquare]; ring
  have shift : (∫ a : ℝ in k..k+1, C d a state) = ∫ u : ℝ in 0..1, f u := by
    simpa only [f, zero_add, add_comm] using
      (intervalIntegral.integral_comp_add_left (f := fun a : ℝ => C d a state) k
        (a := (0 : ℝ)) (b := 1)).symm
  unfold endpointRemainder cell
  change ‖C d k state-(∫ a : ℝ in k..(n : ℝ)+2, C d a state)-
    (1/2 : ℝ) • (C d k state-C d ((n : ℝ)+2) state)‖ ≤ _
  rw [show (n : ℝ)+2=k+1 by dsimp [k]; ring, shift]
  exact (affine_cell_bound f _ w regular _ (div_nonneg cost₀ (sq_nonneg k)) lineError).trans_eq
    (by change 2*(cost/k^2) = 2*cost/k^2; ring)

private theorem inverse_square_prefix (M : Nat) (positive : 0 < M) (J : Nat) :
    (∑ j ∈ Finset.range J, 1/(((M+j : Nat) : ℝ)+1)^2) ≤ 1/(M : ℝ) := by
  let edge := fun j : Nat => 1/((M+j : Nat) : ℝ)
  have telescope (L : Nat) : (∑ j ∈ Finset.range L, (edge j-edge (j+1))) = edge 0-edge L := by
    induction L with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_self]
    | succ L ih => rw [Finset.sum_range_succ, ih]; abel
  calc
    _ ≤ ∑ j ∈ Finset.range J, (edge j-edge (j+1)) := by
      apply Finset.sum_le_sum
      intro j _
      let a : ℝ := ((M+j : Nat) : ℝ)
      have ap : 0 < a := by
        change 0 < ((M+j : Nat) : ℝ)
        exact_mod_cast positive.trans_le (Nat.le_add_right M j)
      change 1/(a+1)^2 ≤ 1/a-1/((M+(j+1) : Nat) : ℝ)
      rw [show ((M+(j+1) : Nat) : ℝ) = a+1 by simp only [a, Nat.cast_add, Nat.cast_one, add_assoc]]
      have next : 0 < a+1 := by positivity
      rw [show 1/a-1/(a+1) = 1/(a*(a+1)) by
        field_simp [ap.ne', next.ne']
        ring]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = edge 0-edge J := telescope J
    _ ≤ 1/(M : ℝ) := by
      simpa only [edge, Nat.add_zero] using
        sub_le_self (1/(M : ℝ)) (one_div_nonneg.mpr (Nat.cast_nonneg (M+J)))

/-- The half-endpoint term and an inverse-cutoff error follow from the actual
unit-scale variation of the channel velocity. -/
theorem directional_source_endpoint_rate (d : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => D h state) velocity 0)
    (B : ℝ) (budget : 0 ≤ B)
    (move : ∀ h ∈ Icc (0 : ℝ) 1,
      ‖D (d*h) (d • velocity-(1/2 : ℝ) • state)-(d • velocity-(1/2 : ℝ) • state)‖ ≤ B*Real.sqrt h) :
    ∃ limit : BurnolL2, Tendsto (finite d state) atTop (𝓝 limit) ∧
      ∀ M : Nat, 0 < M →
        ‖limit-finite d state (M+1)-(1/2 : ℝ) • C d ((M : ℝ)+1) state‖ ≤
          (2*(B+(3/2)*‖d • velocity-(1/2 : ℝ) • state‖))/(M : ℝ) := by
  refine ⟨sourceValue d state, source_tendsto d state velocity source, ?_⟩
  intro M positive
  let cost := 2*(B+(3/2)*‖d • velocity-(1/2 : ℝ) • state‖)
  have cost₀ : 0 ≤ cost := by dsimp [cost]; positivity
  have sums (J : Nat) : ‖∑ j ∈ Finset.range J, endpointRemainder d state (M+j)‖ ≤ cost/(M : ℝ) := calc
    _ ≤ ∑ j ∈ Finset.range J, ‖endpointRemainder d state (M+j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, cost*(1/(((M+j : Nat) : ℝ)+1)^2) :=
      Finset.sum_le_sum fun j _ => (endpoint_cell_rate d state velocity source B budget move (M+j)).trans_eq
        (by change cost/_ = _; rw [div_eq_mul_one_div])
    _ ≤ cost/(M : ℝ) := by
      rw [← Finset.mul_sum, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (inverse_square_prefix M positive J) cost₀
  have counted : Tendsto (fun J => finite d state (M+J+1)) atTop (𝓝 (sourceValue d state)) := by
    simpa only [Function.comp_def, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (source_tendsto d state velocity source).comp (tendsto_add_atTop_nat (M+1))
  have edge := (endpoint_channel_zero d state M).const_sub (C d ((M : ℝ)+1) state)
  have residual := ((counted.sub_const (finite d state (M+1))).sub (edge.const_smul (1/2 : ℝ))).norm
  rw [sub_zero] at residual
  exact le_of_tendsto' residual (fun J => (endpoint_prefix d state velocity source M J).symm ▸ sums J)

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
