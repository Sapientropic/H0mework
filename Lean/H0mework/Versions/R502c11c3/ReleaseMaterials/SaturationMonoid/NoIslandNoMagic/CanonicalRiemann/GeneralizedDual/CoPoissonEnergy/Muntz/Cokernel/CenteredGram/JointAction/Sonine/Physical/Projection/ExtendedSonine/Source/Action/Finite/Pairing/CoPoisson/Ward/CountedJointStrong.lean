import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.JointWardReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedEvaluator
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section

private theorem dilation_derivative (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0) (h : ℝ) :
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation t state)
      (burnolMultiplicativeDilation h velocity) h := by
  have moved := ((burnolMultiplicativeDilation h).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 source
  have movedAt : HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation h (burnolMultiplicativeDilation t state)) (burnolMultiplicativeDilation h velocity) 0 := by simpa using! moved
  have shifted := movedAt.scomp_of_eq h ((hasDerivAt_id h).sub_const h) (by simp)
  convert! shifted using 1
  · funext t
    change burnolMultiplicativeDilation t state =
      burnolMultiplicativeDilation h (burnolMultiplicativeDilation (t - h) state)
    rw [burnolMultiplicativeDilation_add]
    congr 1
    ring
  · simp

private def channelSlope (direction a : ℝ) (state velocity : BurnolL2) : BurnolL2 :=
  (a ^ (-(3 / 2 : ℝ))) • burnolMultiplicativeDilation (direction * Real.log a)
    (direction • velocity - (1 / 2 : ℝ) • state)

private theorem channel_derivative (direction : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0)
    {a : ℝ} (positive : 0 < a) :
    HasDerivAt (fun t : ℝ => ContinuousChannels.channel direction t state)
      (channelSlope direction a state velocity) a := by
  have scale := Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl positive.ne')
  have orbit := (dilation_derivative state velocity source (direction * Real.log a)).scomp a
    ((Real.hasDerivAt_log positive.ne').const_mul direction)
  have actual := scale.smul orbit
  have power : a ^ (-(1 / 2 : ℝ)) * a⁻¹ = a ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add positive]
    norm_num
  have slope : (-(1 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ) - 1)) •
        burnolMultiplicativeDilation (direction * Real.log a) state +
      a ^ (-(1 / 2 : ℝ)) • ((direction * a⁻¹) •
        burnolMultiplicativeDilation (direction * Real.log a) velocity) =
        channelSlope direction a state velocity := by
    unfold channelSlope
    have realLinear (z : ℝ) (v : BurnolL2) :
        burnolMultiplicativeDilation (direction * Real.log a) (z • v) =
          z • burnolMultiplicativeDilation (direction * Real.log a) v :=
      ((burnolMultiplicativeDilation (direction * Real.log a)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).map_smul z v
    rw [map_sub, realLinear, realLinear]
    simp only [smul_sub, smul_smul]
    rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]
    rw [show a ^ (-(1 / 2 : ℝ)) * (direction * a⁻¹) =
      direction * a ^ (-(3 / 2 : ℝ)) by linear_combination direction * power]
    module
  have regular : HasDerivAt
      (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) • burnolMultiplicativeDilation (direction * Real.log t) state)
      (channelSlope direction a state velocity) a := by
    convert! actual using 1
    simpa only [Function.comp_apply, add_comm] using slope.symm
  apply regular.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds positive] with t ht
  rw [ContinuousChannels.channel, ← Complex.ofReal_inv, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  simpa using! (RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.sqrt t)⁻¹
    (burnolMultiplicativeDilation (direction * Real.log t) state)).symm

private theorem channel_continuous (direction : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0) :
    ContinuousOn (fun a : ℝ => ContinuousChannels.channel direction a state) (Ioi 0) :=
  fun _a positive => (channel_derivative direction state velocity source positive).continuousAt.continuousWithinAt

private theorem channel_slope_bound (direction : ℝ) (state velocity : BurnolL2)
    {n a : ℝ} (positive : 0 < n) (after : n ≤ a) :
    ‖channelSlope direction a state velocity‖ ≤
      n ^ (-(3 / 2 : ℝ)) * ‖direction • velocity - (1 / 2 : ℝ) • state‖ := by
  rw [channelSlope, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (positive.le.trans after) _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos positive after (by norm_num)) (norm_nonneg _)

private def cell (direction : ℝ) (state : BurnolL2) (n : ℕ) : BurnolL2 :=
  ContinuousChannels.channel direction ((n : ℝ) + 1) state -
    ∫ a : ℝ in ((n : ℝ) + 1)..((n : ℝ) + 2), ContinuousChannels.channel direction a state

private theorem cell_bound (direction : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0) (n : ℕ) :
    ‖cell direction state n‖ ≤
      ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) * ‖direction • velocity - (1 / 2 : ℝ) • state‖ := by
  have positive : (0 : ℝ) < n + 1 := by positivity
  have ordered : (n : ℝ) + 1 ≤ n + 2 := by linarith
  have regular : IntervalIntegrable (fun a : ℝ => ContinuousChannels.channel direction a state)
      volume ((n : ℝ) + 1) ((n : ℝ) + 2) :=
    ((channel_continuous direction state velocity source).mono
      (fun _ inside => positive.trans_le inside.1)).intervalIntegrable_of_Icc ordered
  have identity : cell direction state n = ∫ a : ℝ in ((n : ℝ) + 1)..((n : ℝ) + 2),
      ContinuousChannels.channel direction ((n : ℝ) + 1) state -
        ContinuousChannels.channel direction a state := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const regular, intervalIntegral.integral_const]
    simp only [show ((n : ℝ) + 2) - ((n : ℝ) + 1) = 1 by ring, one_smul]
    rfl
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun a : ℝ => ContinuousChannels.channel direction a state)
    (f' := fun a => channelSlope direction a state velocity)
    (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (fun _ inside => (channel_derivative direction state velocity source
      (positive.trans_le inside.1)).hasDerivWithinAt)
    (fun _ inside => channel_slope_bound direction state velocity positive inside.1)
  rw [identity]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun a inside => ?_)).trans_eq
    (by rw [show ((n : ℝ) + 2) - ((n : ℝ) + 1) = 1 by ring, abs_one, mul_one])
  have located : a ∈ Icc ((n : ℝ) + 1) ((n : ℝ) + 2) :=
    Ioc_subset_Icc_self (by simpa only [uIoc_of_le ordered] using inside)
  rw [norm_sub_rev]
  exact (estimate a located).trans (mul_le_of_le_one_right
    (mul_nonneg (Real.rpow_nonneg positive.le _) (norm_nonneg _)) (by linarith [located.2]))

private theorem cells_summable (direction : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0) :
    Summable (cell direction state) := by
  have powers : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
  exact (powers.mul_right ‖direction • velocity - (1 / 2 : ℝ) • state‖).of_norm_bounded
    (cell_bound direction state velocity source)

private theorem finite_cells (direction : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0) (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 (N + 1), ContinuousChannels.channel direction (n : ℝ) state) -
        ∫ a : ℝ in Ioc 0 ((N + 1 : ℕ) : ℝ), ContinuousChannels.channel direction a state =
      (∑ n ∈ Finset.range N, cell direction state n) -
        ∫ a : ℝ in Ioc 0 1, ContinuousChannels.channel direction a state := by
  have ordered : (1 : ℝ) ≤ N + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have regular : IntervalIntegrable (fun a : ℝ => ContinuousChannels.channel direction a state)
      volume 1 ((N : ℝ) + 1) :=
    ((channel_continuous direction state velocity source).mono
      (fun _ inside => (by norm_num : (0 : ℝ) < 1).trans_le inside.1)).intervalIntegrable_of_Icc ordered
  have head : IntervalIntegrable (fun a : ℝ => ContinuousChannels.channel direction a state) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ContinuousChannels.channel_integrable direction 1 state
  have adjacent := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := fun n : ℕ => (n : ℝ) + 1) (n := N) (f := fun a => ContinuousChannels.channel direction a state)
    (fun n _ => ((channel_continuous direction state velocity source).mono
      (show Icc ((n : ℝ) + 1) (((n + 1 : ℕ) : ℝ) + 1) ⊆ Ioi 0 from
        fun _ inside => (by positivity : (0 : ℝ) < n + 1).trans_le inside.1)).intervalIntegrable_of_Icc
          (by push_cast; linarith))
  simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at adjacent
  have whole := intervalIntegral.integral_add_adjacent_intervals head regular
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ N + 1 by positivity),
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), ← whole]
  simp only [cell, Finset.sum_sub_distrib]
  rw [show (fun n : ℕ => ∫ a : ℝ in ((n : ℝ) + 1)..((n : ℝ) + 2),
      ContinuousChannels.channel direction a state) =
      fun n : ℕ => ∫ a : ℝ in ((n : ℝ) + 1)..((n : ℝ) + 1 + 1),
        ContinuousChannels.channel direction a state by
      funext n
      rw [show (n : ℝ) + 2 = (n : ℝ) + 1 + 1 by ring]]
  rw [adjacent]
  abel

private def sourceValue (direction : ℝ) (state : BurnolL2) : BurnolL2 :=
  (∑' n : ℕ, cell direction state n) -
    ∫ a : ℝ in Ioc 0 1, ContinuousChannels.channel direction a state

private theorem source_tendsto (direction : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel direction (n : ℝ) state) -
        ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel direction a state) atTop
      (𝓝 (sourceValue direction state)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact ((cells_summable direction state velocity source).hasSum.tendsto_sum_nat.sub_const
    (∫ a : ℝ in Ioc 0 1, ContinuousChannels.channel direction a state)).congr'
      (Eventually.of_forall (fun N => (finite_cells direction state velocity source N).symm))

def value (direction : ℝ) (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : BurnolL2 :=
  sourceValue direction (JointCounting.value coordinate zero)

/-- The actual Euler velocity makes the complete second arithmetic source strongly convergent. -/
theorem original_forward_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (JointCounting.value coordinate zero)) atTop
      (𝓝 (value (-1) coordinate zero)) := by
  have actual := source_tendsto (-1) (JointCounting.value coordinate zero)
    (CountedEulerDomain.jointVelocity coordinate zero)
    (CountedEulerDomain.joint_strong_derivative coordinate zero)
  simpa only [FiniteForcing.source, Channels.sourceChannel, ContinuousChannels.normalization,
    ContinuousChannels.channel, neg_one_mul, value] using! actual

/-- The same whole cell construction retains every reverse continuous channel. -/
theorem original_reverse_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => DualSource.source N (JointCounting.value coordinate zero)) atTop
      (𝓝 (value 1 coordinate zero)) :=
  source_tendsto 1 (JointCounting.value coordinate zero)
    (CountedEulerDomain.jointVelocity coordinate zero)
    (CountedEulerDomain.joint_strong_derivative coordinate zero)

/-- The original finite normal pair is consumed by the two complete second-source limits. -/
theorem original_gram (left right : BurnolCompletedMellinCoordinate)
    (leftZero : riemannZeta left.value = 0) (rightZero : riemannZeta right.value = 0) :
    inner ℂ (value (-1) left leftZero) (value (-1) right rightZero) =
      inner ℂ (value 1 left leftZero) (value 1 right rightZero) := by
  have forward := (original_forward_tendsto left leftZero).inner (𝕜 := ℂ)
    (original_forward_tendsto right rightZero)
  have reverse := (original_reverse_tendsto left leftZero).inner (𝕜 := ℂ)
    (original_reverse_tendsto right rightZero)
  exact tendsto_nhds_unique
    (forward.congr' (Eventually.of_forall fun N => DualSourceGram.finite_gram N _ _)) reverse

/-- The already generated independent response reads the complete second source. -/
theorem original_response (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (side : Bool) :
    inner ℂ (value (-1) coordinate zero)
      (burnolQuarterZeroExtension (ResponseProfile.state side : BurnolQuarterIntervalL2)) =
      inner ℂ (JointCounting.value coordinate zero) (ResponseCounting.value side) := by
  have complete := (original_forward_tendsto coordinate zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := burnolQuarterZeroExtension (ResponseProfile.state side : BurnolQuarterIntervalL2)))
  exact tendsto_nhds_unique complete (ResponseCounting.joint_forward_pairing_tendsto coordinate zero side)

/-- The original two-sided Ward consumes the actual source value, including its entire density. -/
theorem original_ward (left right : BurnolCompletedMellinCoordinate)
    (leftZero : riemannZeta left.value = 0) (rightZero : riemannZeta right.value = 0) :
    let jl := JointCounting.value left leftZero
    let jr := JointCounting.value right rightZero
    let tl := OriginalRieszSource.Kernel.A left • CountingDual.value left -
      OriginalRieszSource.Kernel.beta left • PositionCounting.value left leftZero
    let tr := OriginalRieszSource.Kernel.A right • CountingDual.value right -
      OriginalRieszSource.Kernel.beta right • PositionCounting.value right rightZero
    let eu := burnolQuarterZeroExtension (OriginalRieszSource.Response.u : BurnolQuarterIntervalL2)
    star (star left.value - 1 / 2) * inner ℂ tl jr +
      (star right.value - 1 / 2) * inner ℂ jl tr +
      star (OriginalRieszSource.Kernel.A left ^ 2 - OriginalRieszSource.Kernel.beta left ^ 2) *
        star (inner ℂ (value (-1) right rightZero) eu) +
      (OriginalRieszSource.Kernel.A right ^ 2 - OriginalRieszSource.Kernel.beta right ^ 2) *
        inner ℂ (value (-1) left leftZero) eu = 0 := by
  dsimp only
  have leftRead := (original_forward_tendsto left leftZero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := burnolQuarterZeroExtension (OriginalRieszSource.Response.u : BurnolQuarterIntervalL2)))
  have rightRead := (original_forward_tendsto right rightZero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := burnolQuarterZeroExtension (OriginalRieszSource.Response.u : BurnolQuarterIntervalL2)))
  apply tendsto_nhds_unique _ (JointWardReadback.original_forward_limit left right leftZero rightZero)
  exact ((tendsto_const_nhds.add
    (rightRead.star.const_mul (star (OriginalRieszSource.Kernel.A left ^ 2 -
      OriginalRieszSource.Kernel.beta left ^ 2))))).add
    (leftRead.const_mul (OriginalRieszSource.Kernel.A right ^ 2 - OriginalRieszSource.Kernel.beta right ^ 2))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
