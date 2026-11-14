import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointCell

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong

open Complex Filter MeasureTheory Set
open scoped Topology

open private endpointRemainder endpoint_cell_eventually channel_scale_apply channel_scale_norm from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointCell
open private cell finite_cells sourceValue source_tendsto from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong
open private cell_power_tail from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.TailRate

local notation "C" => ContinuousChannels.channel
local notation "D" => burnolMultiplicativeDilation
local notation "finite" => fun d (v : BurnolL2) (N : Nat) =>
  (∑ n ∈ Finset.Ico 1 N, C d (n : ℝ) v) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), C d a v

private theorem endpoint_prefix (d : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => D h state) velocity 0) (M J : Nat) :
    finite d state (M+J+1)-finite d state (M+1)-
      (1/2 : ℝ) • (C d ((M : ℝ)+1) state-C d (((M+J : Nat) : ℝ)+1) state) =
        ∑ j ∈ Finset.range J, endpointRemainder d state (M+j) := by
  let edge := fun j : Nat => C d (((M+j : Nat) : ℝ)+1) state
  have telescope (L : Nat) : (∑ j ∈ Finset.range L, (edge j-edge (j+1))) = edge 0-edge L := by
    induction L with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_self]
    | succ L ih => rw [Finset.sum_range_succ, ih]; abel
  dsimp only
  rw [finite_cells d state velocity source (M+J), finite_cells d state velocity source M]
  simp only [endpointRemainder, Finset.sum_sub_distrib, ← Finset.smul_sum]
  have edgeRead (j : Nat) : C d (((M+j : Nat) : ℝ)+2) state = edge (j+1) := by
    dsimp only [edge]
    rw [show ((M+j : Nat) : ℝ)+2 = ((M+(j+1) : Nat) : ℝ)+1 by push_cast; ring]
  simp_rw [edgeRead]
  have endpoints := telescope J
  rw [Finset.sum_sub_distrib] at endpoints
  change _ = _-(1/2 : ℝ) •
    ((∑ j ∈ Finset.range J, edge j)-(∑ j ∈ Finset.range J, edge (j+1)))
  rw [endpoints, Finset.sum_range_add]
  dsimp only [edge]
  simp only [Nat.add_zero]
  abel

private theorem endpoint_channel_zero (d : ℝ) (state : BurnolL2) (M : Nat) :
    Tendsto (fun j : Nat => C d (((M+j : Nat) : ℝ)+1) state) atTop (𝓝 0) := by
  have indices : Tendsto (fun j : Nat => ((M+j : Nat) : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_left_comm, add_assoc, add_comm] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat (M+1))
  have norms := ((tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp indices)).mul_const ‖state‖)
  rw [zero_mul] at norms
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply norms.congr'
  filter_upwards with j
  rw [← channel_scale_apply, channel_scale_norm]
  rfl

private theorem endpoint_tail_bound (d : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => D h state) velocity 0)
    (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ M : Nat in atTop,
      ‖sourceValue d state-finite d state (M+1)-(1/2 : ℝ) • C d ((M : ℝ)+1) state‖ ≤
        (4*ε)*(M : ℝ)^(-(1/2 : ℝ)) := by
  obtain ⟨M₀, ready⟩ := eventually_atTop.mp (endpoint_cell_eventually d state velocity source ε positive)
  filter_upwards [eventually_ge_atTop M₀, eventually_ge_atTop (1 : Nat)] with M big one
  have each (j : Nat) : ‖endpointRemainder d state (M+j)‖ ≤
      (2*ε)*(((M+j : Nat) : ℝ)+1)^(-(3/2 : ℝ)) := ready _ (big.trans (Nat.le_add_right M j))
  have powers : Summable (fun j : Nat => (((M+j : Nat) : ℝ)+1)^(-(3/2 : ℝ))) := by
    have same (j : Nat) : ((j+(M+1) : Nat) : ℝ) = ((M+j : Nat) : ℝ)+1 := by
      push_cast
      ring
    simpa only [same] using
      (summable_nat_add_iff (M+1)).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ) < -1))
  have tail : (∑' j : Nat, (((M+j : Nat) : ℝ)+1)^(-(3/2 : ℝ))) ≤ 2*(M : ℝ)^(-(1/2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm ((M : ℝ))] using
      cell_power_tail M (zero_lt_one.trans_le one)
  have sums (J : Nat) : ‖∑ j ∈ Finset.range J, endpointRemainder d state (M+j)‖ ≤
      (4*ε)*(M : ℝ)^(-(1/2 : ℝ)) := calc
    _ ≤ ∑ j ∈ Finset.range J, ‖endpointRemainder d state (M+j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, (2*ε)*(((M+j : Nat) : ℝ)+1)^(-(3/2 : ℝ)) :=
      Finset.sum_le_sum fun j _ => each j
    _ ≤ (2*ε)*(∑' j : Nat, (((M+j : Nat) : ℝ)+1)^(-(3/2 : ℝ))) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (powers.sum_le_tsum (Finset.range J) fun j _ => Real.rpow_nonneg (by positivity) _)
        (by positivity)
    _ ≤ _ := (mul_le_mul_of_nonneg_left tail (by positivity)).trans_eq (by ring)
  have counted : Tendsto (fun J => finite d state (M+J+1)) atTop (𝓝 (sourceValue d state)) := by
    simpa only [Function.comp_def, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (source_tendsto d state velocity source).comp (tendsto_add_atTop_nat (M+1))
  have edge := (endpoint_channel_zero d state M).const_sub (C d ((M : ℝ)+1) state)
  have residual := ((counted.sub_const (finite d state (M+1))).sub (edge.const_smul (1/2 : ℝ))).norm
  rw [sub_zero] at residual
  exact le_of_tendsto' residual (fun J => (endpoint_prefix d state velocity source M J).symm ▸ sums J)

/-- Undo the channel scale at the actual counting cutoff. -/
def countEndpointScale (d : ℝ) (N : Nat) : BurnolL2 →L[ℂ] BurnolL2 :=
  (Real.sqrt (N : ℝ) : ℂ) • (D (-(d*Real.log (N : ℝ)))).toContinuousLinearEquiv.toContinuousLinearMap

theorem count_endpoint_scale_norm (d : ℝ) (N : Nat) (value : BurnolL2) :
    ‖countEndpointScale d N value‖ = Real.sqrt (N : ℝ)*‖value‖ := by
  change ‖(Real.sqrt (N : ℝ) : ℂ) • D (-(d*Real.log (N : ℝ))) value‖ = _
  rw [norm_smul, LinearIsometryEquiv.norm_map, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

private theorem count_endpoint_scale_channel (d : ℝ) (N : Nat) (positive : 0 < N) (state : BurnolL2) :
    countEndpointScale d N (C d (N : ℝ) state) = state := by
  have nonzero : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast positive)).ne'
  change (Real.sqrt (N : ℝ) : ℂ) • D (-(d*Real.log (N : ℝ))) (C d (N : ℝ) state) = state
  rw [ContinuousChannels.channel, map_smul, burnolMultiplicativeDilation_add,
    neg_add_cancel, burnolMultiplicativeDilation_zero, smul_smul, mul_inv_cancel₀ nonzero, one_smul]

private theorem root_tail_le (M : Nat) (positive : 0 < M) :
    Real.sqrt ((M : ℝ)+1)*(M : ℝ)^(-(1/2 : ℝ)) ≤ 2 := by
  have live : 0 < (M : ℝ) := by exact_mod_cast positive
  have large : (1 : ℝ) ≤ M := by exact_mod_cast positive
  have below : Real.sqrt ((M : ℝ)+1) ≤ 2*Real.sqrt M := by
    refine (Real.sqrt_le_sqrt (show (M : ℝ)+1 ≤ 4*M by linarith)).trans_eq ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [Real.rpow_neg live.le, ← Real.sqrt_eq_rpow]
  exact (mul_le_mul_of_nonneg_right below (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq
    (by rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr live).ne', mul_one])

/-- After undoing the actual cutoff dilation, the full count tail converges to half of its source field. -/
theorem directional_source_endpoint_limit (d : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => D h state) velocity 0) :
    Tendsto (fun M : Nat => countEndpointScale d (M+1) (sourceValue d state-finite d state (M+1)))
      atTop (𝓝 ((1/2 : ℝ) • state)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun _ => hb.trans_le (norm_nonneg _)
  · intro b hb
    have ε : 0 < b/16 := by positivity
    filter_upwards [endpoint_tail_bound d state velocity source (b/16) ε, eventually_ge_atTop (1 : Nat)]
      with M tail positive
    let w := sourceValue d state-finite d state (M+1)
    let v := C d ((M : ℝ)+1) state
    have endpoint : countEndpointScale d (M+1) v = state := by
      simpa only [v, Nat.cast_add, Nat.cast_one] using
        count_endpoint_scale_channel d (M+1) (by omega) state
    change ‖countEndpointScale d (M+1) w-(1/2 : ℝ) • state‖ < b
    have linear : countEndpointScale d (M+1) (w-(1/2 : ℝ) • v) =
        countEndpointScale d (M+1) w-(1/2 : ℝ) • state := by
      have realLinear : countEndpointScale d (M+1) ((1/2 : ℝ) • v) =
          (1/2 : ℝ) • countEndpointScale d (M+1) v :=
        ((countEndpointScale d (M+1)).restrictScalars ℝ).map_smul (1/2 : ℝ) v
      rw [map_sub, realLinear, endpoint]
    rw [← linear, count_endpoint_scale_norm, Nat.cast_add, Nat.cast_one]
    have bound := mul_le_mul_of_nonneg_left tail (Real.sqrt_nonneg ((M : ℝ)+1))
    change Real.sqrt ((M : ℝ)+1)*‖w-(1/2 : ℝ) • v‖ ≤ _ at bound
    refine (bound.trans ?_).trans_lt (show b/2 < b by linarith)
    calc
      _ = (4*(b/16))*(Real.sqrt ((M : ℝ)+1)*(M : ℝ)^(-(1/2 : ℝ))) := by ring
      _ ≤ (4*(b/16))*2 := mul_le_mul_of_nonneg_left (root_tail_le M (by omega)) (by positivity)
      _ = b/2 := by ring

/-- An actual R action supplies the channel derivative; the original count
limit is consumed at the same input. -/
theorem actual_resolvent_counted_endpoint_limit (c : BurnolCompletedMellinCoordinate)
    (input limit : BurnolL2)
    (counted : Tendsto (fun N => DualSource.source N (burnolDirectRightResolventCLM c input))
      atTop (𝓝 limit)) :
    Tendsto (fun M : Nat => countEndpointScale 1 (M+1)
      (limit-DualSource.source (M+1) (burnolDirectRightResolventCLM c input)))
      atTop (𝓝 ((1/2 : ℝ) • burnolDirectRightResolventCLM c input)) := by
  let y := burnolDirectRightResolventCLM c input
  let v := (-2 : ℝ) • ((c.value/2-1/4) • y+input)
  have param : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have derivative : HasDerivAt (fun h : ℝ => D h y) v 0 := by
    have actual := (burnolDirectRightResolventOrbit_hasDerivAt (c.value/2) param input).scomp_of_eq 0
      ((hasDerivAt_id (0 : ℝ)).const_mul (-2)) (by norm_num)
    simp only [mul_one, Function.comp_def, id_eq] at actual
    have path : (fun h : ℝ => D (-(-2*h)/2) (burnolDirectRightResolvent (c.value/2) input)) =
        fun h => D h y := by
      funext h
      rw [show -(-2*h)/2=h by ring]
      rfl
    rw [path] at actual
    change HasDerivAt (fun h : ℝ => D h y) v 0 at actual
    exact actual
  have same : limit = sourceValue 1 y :=
    tendsto_nhds_unique counted (source_tendsto 1 y v derivative)
  rw [same]
  exact directional_source_endpoint_limit 1 y v derivative

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
