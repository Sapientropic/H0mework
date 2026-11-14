import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.Slope
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Topological.Quadrature.SecondEndpoint
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong

open Filter Set MeasureTheory
attribute [local instance 1200] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
open scoped Topology

open private channelSlope channel_derivative sourceValue source_tendsto from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong
open private endpointRemainder channelScale channel_scale_apply channel_scale_norm channel_mul_scale from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointCell
open private endpoint_prefix endpoint_channel_zero root_tail_le count_endpoint_scale_channel from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointLimit
open private slopeSeed curveSeed curve slope_derivative slope_limit_at_infty from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.Slope

local notation "D" => burnolMultiplicativeDilation
local notation "C" => ContinuousChannels.channel
local notation "finite" => fun d (v : BurnolL2) (N : Nat) =>
  (∑ n ∈ Finset.Ico 1 N, C d (n : ℝ) v) - ∫ a : ℝ in Ioc 0 (N : ℝ), C d a v

private def correctedCell (d : ℝ) (state velocity : BurnolL2) (n : Nat) : BurnolL2 :=
  endpointRemainder d state n +
    (1/12 : ℝ) • (channelSlope d ((n : ℝ)+1) state velocity - channelSlope d ((n : ℝ)+2) state velocity)

private theorem curve_continuous_at_one (d : ℝ) (state velocity acceleration : BurnolL2) :
    ContinuousAt (curve d state velocity acceleration) 1 := by
  unfold curve
  exact (continuousAt_id.rpow_const (Or.inl one_ne_zero)).smul
    ((burnolMultiplicativeDilation_stronglyContinuous _).continuousAt.comp
      ((Real.continuousAt_log one_ne_zero).const_mul d))

private theorem curve_continuous_on (d : ℝ) (state velocity acceleration : BurnolL2) :
    ContinuousOn (curve d state velocity acceleration) (Ioi 0) := by
  intro a positive
  unfold curve
  apply ContinuousAt.continuousWithinAt
  exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt positive))).smul
    ((burnolMultiplicativeDilation_stronglyContinuous _).continuousAt.comp
      ((Real.continuousAt_log (ne_of_gt positive)).const_mul d))

private theorem slope_scale (d k t : ℝ) (kp : 0 < k) (tp : 0 < t) (state velocity : BurnolL2) :
    channelSlope d (k*t) state velocity = k⁻¹ • channelScale d k (channelSlope d t state velocity) := by
  let v := slopeSeed d state velocity
  have asChannel (x : ℝ) (xp : 0 < x) :
      channelSlope d x state velocity = x⁻¹ • C d x v := by
    have channel : C d x v = (Real.sqrt x)⁻¹ • D (d*Real.log x) v := by
      rw [ContinuousChannels.channel, ← Complex.ofReal_inv]
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.sqrt x)⁻¹ _).symm
    change x^(-(3/2 : ℝ)) • D (d*Real.log x) v = x⁻¹ • C d x v
    rw [channel, smul_smul, Real.sqrt_eq_rpow, ← Real.rpow_neg xp.le,
      ← Real.rpow_neg_one, ← Real.rpow_add xp]
    norm_num
  rw [asChannel _ (mul_pos kp tp), asChannel _ tp, channel_mul_scale d k t kp tp, map_smul, smul_smul, mul_inv]

private theorem local_cell_bound (d : ℝ) (state velocity acceleration : BurnolL2)
    (first : HasDerivAt (fun h : ℝ => D h state) velocity 0)
    (second : HasDerivAt (fun h : ℝ => D h velocity) acceleration 0)
    (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ‖correctedCell d state velocity n‖ ≤ ε*((n : ℝ)+1)^(-(5/2 : ℝ)) := by
  let g := curve d state velocity acceleration
  obtain ⟨δ, δpos, close⟩ :=
    Metric.continuousAt_iff.mp (curve_continuous_at_one d state velocity acceleration) ε positive
  have indices : Tendsto (fun n : Nat => (n : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  filter_upwards [(tendsto_inv_atTop_zero.comp indices).eventually (eventually_lt_nhds δpos)]
    with n narrow
  let k : ℝ := (n : ℝ)+1
  let f := fun u : ℝ => C d (1+u/k) state
  let f' := fun u : ℝ => k⁻¹ • channelSlope d (1+u/k) state velocity
  let f'' := fun u : ℝ => (k⁻¹)^2 • g (1+u/k)
  have kp : 0 < k := by dsimp [k]; positivity
  have k₀ (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) : 0 < 1+u/k := by positivity [inside.1]
  have arg (u : ℝ) : HasDerivAt (fun t : ℝ => 1+t/k) k⁻¹ u := by
    simpa only [one_div, id_eq] using ((hasDerivAt_id u).div_const k).const_add 1
  have deriv (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' u) u := by
    have computed := (channel_derivative d state velocity first (k₀ u inside)).scomp u (arg u)
    exact computed
  have slope (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) : HasDerivAt f' (f'' u) u := by
    have c := ((slope_derivative d state velocity acceleration first second (k₀ u inside)).scomp u (arg u)).const_smul k⁻¹
    change HasDerivAt f' (k⁻¹ • (k⁻¹ • g (1+u/k))) u at c
    rwa [smul_smul, ← pow_two] at c
  have fCont : ContinuousOn f (Icc (0 : ℝ) 1) := fun u inside =>
    (deriv u inside).continuousAt.continuousWithinAt
  have cont : ContinuousOn f'' (Icc (0 : ℝ) 1) := by
    have affine : Continuous (fun t : ℝ => 1+t/k) := by fun_prop
    have moved : ContinuousOn (fun u : ℝ => g (1+u/k)) (Icc (0 : ℝ) 1) :=
      (curve_continuous_on d state velocity acceleration).comp affine.continuousOn
        (fun u inside => k₀ u inside)
    have constant : ContinuousOn (fun _ : ℝ => (k⁻¹)^2) (Icc (0 : ℝ) 1) := continuousOn_const
    have scaled := constant.smul moved
    exact scaled
  have error (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) : ‖f'' u-f'' 0‖ ≤ (k⁻¹)^2*ε := by
    have nonneg := div_nonneg inside.1 kp.le
    have upper : u/k ≤ k⁻¹ := by
      simpa only [one_div] using div_le_div_of_nonneg_right inside.2 kp.le
    have near : dist (1+u/k) (1 : ℝ) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg nonneg]
      exact upper.trans_lt narrow
    have tiny := close near
    rw [dist_eq_norm] at tiny
    simp only [f'', zero_div, add_zero, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (sq_nonneg k⁻¹)]
    exact mul_le_mul_of_nonneg_left tiny.le (sq_nonneg _)
  have localBound := SourceGeneratedQuadrature.second_endpoint_bound f f' f'' deriv slope cont
    error
  have eval (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) :
      C d (k+u) state = channelScale d k (f u) := by
    rw [show k+u=k*(1+u/k) by field_simp [kp.ne']]
    exact channel_mul_scale d k _ kp (k₀ u inside) state
  have slopeEval (u : ℝ) (inside : u ∈ Icc (0 : ℝ) 1) :
      channelSlope d (k+u) state velocity = channelScale d k (f' u) := by
    rw [show k+u=k*(1+u/k) by field_simp [kp.ne'], slope_scale d k _ kp (k₀ u inside)]
    exact (map_smul (channelScale d k) _ _).symm
  have integrals : (∫ a : ℝ in k..k+1, C d a state) = channelScale d k (∫ u : ℝ in 0..1, f u) := by
    have shifted : (∫ u : ℝ in (0 : ℝ)..1, C d (k+u) state) =
        ∫ a : ℝ in k..k+1, C d a state := by
      simpa only [zero_add, add_comm] using
        (intervalIntegral.integral_comp_add_left (f := fun a : ℝ => C d a state) k (a := 0) (b := 1))
    have fInt : IntervalIntegrable f volume 0 1 := fCont.intervalIntegrable_of_Icc zero_le_one
    rw [← shifted, ← (channelScale d k).intervalIntegral_comp_comm fInt]
    exact intervalIntegral.integral_congr (fun u inside => eval u (uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1) ▸ inside))
  have cellEq : correctedCell d state velocity n =
      channelScale d k ((1/2 : ℝ) • (f 0+f 1) - (∫ u : ℝ in 0..1, f u) +
        (1/12 : ℝ) • (f' 0-f' 1)) := by
    unfold correctedCell endpointRemainder
    change C d k state - (∫ a : ℝ in k..((n : ℝ)+2), C d a state) -
      (1/2 : ℝ) • (C d k state-C d ((n : ℝ)+2) state) +
      (1/12 : ℝ) • (channelSlope d k state velocity-channelSlope d ((n : ℝ)+2) state velocity) = _
    rw [show (n : ℝ)+2 = k+1 by dsimp [k]; ring, integrals]
    have z := eval 0 (left_mem_Icc.mpr zero_le_one)
    have v := slopeEval 0 (left_mem_Icc.mpr zero_le_one)
    rw [add_zero] at z v
    rw [z, eval 1 (right_mem_Icc.mpr zero_le_one), v, slopeEval 1 (right_mem_Icc.mpr zero_le_one)]
    simp only [map_add, map_sub, map_smul]
    module
  rw [cellEq, channel_scale_norm]
  refine (mul_le_mul_of_nonneg_left localBound (by positivity)).trans_eq ?_
  have powered : (Real.sqrt k)⁻¹*(k⁻¹)^2 = k^(-(5/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg kp.le, ← Real.rpow_neg_one, ← Real.rpow_mul_natCast kp.le,
      ← Real.rpow_add kp]
    norm_num
  calc
    _ = ε*((Real.sqrt k)⁻¹*(k⁻¹)^2) := by ring
    _ = _ := by rw [powered]

private theorem five_halves_tail (M : Nat) (positive : 0 < M) :
    (∑' j : Nat, (((M+j : Nat) : ℝ)+1)^(-(5/2 : ℝ))) ≤
      (2/3 : ℝ)*(M : ℝ)^(-(3/2 : ℝ)) := by
  have start : 0 < (M : ℝ) := by exact_mod_cast positive
  let p := fun x : ℝ => x^(-(5/2 : ℝ))
  have decreasing : AntitoneOn p (Ici (M : ℝ)) := fun _ hx _ _ ordered =>
    Real.rpow_le_rpow_of_nonpos (start.trans_le hx) ordered (by norm_num)
  have integrable := integrableOn_Ioi_rpow_of_lt (a := -(5/2 : ℝ)) (by norm_num) start
  calc
    _ ≤ ∫ x in Ioi (M : ℝ), p x := by
      simpa only [p, Nat.cast_add, Nat.cast_one, add_comm (M : ℝ)] using
        decreasing.tsum_comp_add_le_integral M integrable
          (fun x hx => Real.rpow_nonneg (start.trans hx).le _)
    _ = _ := by
      rw [show (fun x => p x) = fun x => x^(-(5/2 : ℝ)) from rfl,
        integral_Ioi_rpow_of_lt (by norm_num : -(5/2 : ℝ) < -1) start,
        show -(5/2 : ℝ)+1 = -(3/2 : ℝ) by norm_num]
      ring

private theorem tail_prefix (d : ℝ) (state velocity : BurnolL2)
    (first : HasDerivAt (fun h : ℝ => D h state) velocity 0) (M J : Nat) :
    finite d state (M+J+1)-finite d state (M+1)-
        (1/2 : ℝ) • (C d ((M : ℝ)+1) state-C d (((M+J : Nat) : ℝ)+1) state) +
        (1/12 : ℝ) • (channelSlope d ((M : ℝ)+1) state velocity -
          channelSlope d (((M+J : Nat) : ℝ)+1) state velocity) =
      ∑ j ∈ Finset.range J, correctedCell d state velocity (M+j) := by
  rw [endpoint_prefix d state velocity first M J]
  unfold correctedCell
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]
  let edge := fun j : Nat => channelSlope d (((M+j : Nat) : ℝ)+1) state velocity
  have step (j : Nat) : channelSlope d (((M+j : Nat) : ℝ)+2) state velocity = edge (j+1) := by
    dsimp only [edge]
    rw [show (((M+j : Nat) : ℝ)+2) = ((M+(j+1) : Nat) : ℝ)+1 by push_cast; ring]
  simp_rw [step]
  have telescope (L : Nat) : (∑ j ∈ Finset.range L, (edge j-edge (j+1))) = edge 0-edge L := by
    induction L with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_self]
    | succ L ih => rw [Finset.sum_range_succ, ih]; abel
  rw [telescope]
  rfl

private theorem velocity_tail_bound (d : ℝ) (state velocity acceleration : BurnolL2)
    (first : HasDerivAt (fun h : ℝ => D h state) velocity 0)
    (second : HasDerivAt (fun h : ℝ => D h velocity) acceleration 0)
    (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ M : Nat in atTop,
      ‖sourceValue d state-finite d state (M+1)-(1/2 : ℝ) • C d ((M : ℝ)+1) state +
          (1/12 : ℝ) • channelSlope d ((M : ℝ)+1) state velocity‖ ≤
        (2/3*ε)*(M : ℝ)^(-(3/2 : ℝ)) := by
  obtain ⟨start, ready⟩ := eventually_atTop.mp (local_cell_bound d state velocity acceleration first second ε positive)
  filter_upwards [eventually_ge_atTop start, eventually_ge_atTop (1 : Nat)] with M big one
  have each (j : Nat) : ‖correctedCell d state velocity (M+j)‖ ≤
      ε*(((M+j : Nat) : ℝ)+1)^(-(5/2 : ℝ)) := ready _ (big.trans (Nat.le_add_right M j))
  have powers : Summable (fun j : Nat => (((M+j : Nat) : ℝ)+1)^(-(5/2 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm (M : ℝ), add_left_comm] using
      (summable_nat_add_iff (M+1)).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(5/2 : ℝ) < -1))
  have sums (J : Nat) : ‖∑ j ∈ Finset.range J, correctedCell d state velocity (M+j)‖ ≤
      (2/3*ε)*(M : ℝ)^(-(3/2 : ℝ)) := calc
    _ ≤ ∑ j ∈ Finset.range J, ‖correctedCell d state velocity (M+j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, ε*(((M+j : Nat) : ℝ)+1)^(-(5/2 : ℝ)) :=
      Finset.sum_le_sum fun j _ => each j
    _ ≤ ε*(∑' j : Nat, (((M+j : Nat) : ℝ)+1)^(-(5/2 : ℝ))) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (powers.sum_le_tsum (Finset.range J) fun _ _ => Real.rpow_nonneg (by positivity) _) positive.le
    _ ≤ _ := (mul_le_mul_of_nonneg_left (five_halves_tail M (zero_lt_one.trans_le one)) positive.le).trans_eq (by ring)
  have counted : Tendsto (fun J : Nat => finite d state (M+J+1)) atTop (𝓝 (sourceValue d state)) := by
    simpa only [Function.comp_def, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (source_tendsto d state velocity first).comp (tendsto_add_atTop_nat (M+1))
  have edge := (endpoint_channel_zero d state M).const_sub (C d ((M : ℝ)+1) state)
  have slope := (slope_limit_at_infty d state velocity M).const_sub (channelSlope d ((M : ℝ)+1) state velocity)
  have residual := (((counted.sub_const (finite d state (M+1))).sub (edge.const_smul (1/2 : ℝ))).add
    (slope.const_smul (1/12 : ℝ))).norm
  rw [sub_zero, sub_zero] at residual
  exact le_of_tendsto' residual fun J => (tail_prefix d state velocity first M J).symm ▸ sums J

/-- Remove the first endpoint term at its own cutoff, then undo the source
dilation at the next scale to read the genuine directional velocity. -/
theorem directional_source_velocity_limit (d : ℝ) (state velocity acceleration : BurnolL2)
    (first : HasDerivAt (fun h : ℝ => D h state) velocity 0)
    (second : HasDerivAt (fun h : ℝ => D h velocity) acceleration 0) :
    Tendsto (fun M : Nat => ((M : ℝ)+1) •
      countEndpointScale d (M+1) (sourceValue d state-finite d state (M+1)-
        (1/2 : ℝ) • C d ((M : ℝ)+1) state)) atTop
      (𝓝 ((-(1/12 : ℝ)) • slopeSeed d state velocity)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun _ => hb.trans_le (norm_nonneg _)
  · intro b hb
    have ε : 0 < b/8 := by positivity
    filter_upwards [velocity_tail_bound d state velocity acceleration first second (b/8) ε,
      eventually_ge_atTop (1 : Nat)] with M residual positive
    let k : ℝ := (M : ℝ)+1
    let S := countEndpointScale d (M+1)
    let V := slopeSeed d state velocity
    let w := sourceValue d state-finite d state (M+1)-(1/2 : ℝ) • C d k state
    have kPos : 0 < k := by dsimp [k]; positivity
    have slope_as_channel : channelSlope d k state velocity = k⁻¹ • C d k V := by
      have one : channelSlope d 1 state velocity = V := by
        simp only [channelSlope, Real.one_rpow, Real.log_one, mul_zero, burnolMultiplicativeDilation_zero, one_smul]
        rfl
      have scale := slope_scale d k 1 kPos zero_lt_one state velocity
      rw [mul_one, one, channel_scale_apply] at scale
      exact scale
    have reads : k • S (channelSlope d k state velocity) = V := by
      rw [slope_as_channel]
      change k • (S.restrictScalars ℝ) (k⁻¹ • C d k V) = _
      rw [map_smul, smul_smul, mul_inv_cancel₀ kPos.ne', one_smul]
      have e := count_endpoint_scale_channel d (M+1) (by omega) V
      change S (C d k V) = V
      simpa only [Nat.cast_add, Nat.cast_one, k, S] using e
    have scale : k • S (w+(1/12 : ℝ) • channelSlope d k state velocity) =
        k • S w - (-(1/12 : ℝ)) • V := by
      let T := S.restrictScalars ℝ
      change k • T (w+(1/12 : ℝ) • channelSlope d k state velocity) =
        k • T w - (-(1/12 : ℝ)) • V
      have eq : k • T (channelSlope d k state velocity) = V := reads
      rw [map_add, map_smul, smul_add, smul_comm k, eq, neg_smul, sub_neg_eq_add]
    change ‖k • S w - (-(1/12 : ℝ)) • V‖ < b
    rw [← scale, norm_smul, Real.norm_of_nonneg kPos.le, count_endpoint_scale_norm]
    simp only [Nat.cast_add, Nat.cast_one]
    change k*(Real.sqrt k*‖w+(1/12 : ℝ) • channelSlope d k state velocity‖) < b
    have residual' : ‖w+(1/12 : ℝ) • channelSlope d k state velocity‖ ≤
        (2/3*(b/8))*(M : ℝ)^(-(3/2 : ℝ)) := residual
    have bound := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left residual' (Real.sqrt_nonneg k)) kPos.le
    have near : k ≤ 2*(M : ℝ) := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast positive
      dsimp [k]; linarith
    have root : Real.sqrt k*(M : ℝ)^(-(1/2 : ℝ)) ≤ 2 :=
      root_tail_le M positive
    have mp : 0 < (M : ℝ) := by exact_mod_cast positive
    have scaleBound : k*(Real.sqrt k*(M : ℝ)^(-(3/2 : ℝ))) ≤ 4 := by
      rw [show -(3/2 : ℝ) = -1 + -(1/2 : ℝ) by norm_num, Real.rpow_add mp,
        Real.rpow_neg_one]
      calc
        _ = (k*(M : ℝ)⁻¹)*(Real.sqrt k*(M : ℝ)^(-(1/2 : ℝ))) := by ring
        _ ≤ 2*2 := mul_le_mul (by
          apply (mul_le_mul_of_nonneg_right near (inv_nonneg.mpr mp.le)).trans_eq
          rw [mul_assoc, mul_inv_cancel₀ mp.ne', mul_one]) root (by positivity) (by norm_num)
        _ = 4 := by norm_num
    refine bound.trans_lt ?_
    calc
      _ = (k*(Real.sqrt k*(M : ℝ)^(-(3/2 : ℝ))))*(2/3*(b/8)) := by ring
      _ ≤ 4*(2/3*(b/8)) := mul_le_mul_of_nonneg_right scaleBound (by positivity)
      _ < b := by linarith


end OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
