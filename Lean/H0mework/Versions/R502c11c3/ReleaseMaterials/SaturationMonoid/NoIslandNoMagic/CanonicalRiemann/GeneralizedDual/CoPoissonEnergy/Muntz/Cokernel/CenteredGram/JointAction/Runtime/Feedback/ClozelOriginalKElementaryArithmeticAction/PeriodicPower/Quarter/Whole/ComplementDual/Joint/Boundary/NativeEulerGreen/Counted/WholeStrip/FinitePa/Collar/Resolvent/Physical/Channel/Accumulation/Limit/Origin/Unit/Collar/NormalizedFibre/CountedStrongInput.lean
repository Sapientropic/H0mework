import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedSourceTail
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.OriginTrace

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen OriginalRieszSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKCoefficientBFiniteAction
open scoped Topology ENNReal

open private positive_window_L1_bound from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Rate
open private even_cut_reconstruction homogeneous_tail_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit
open private cutoff_split_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
open private complete_even complete_compact from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar
open private compensated_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private count_below_log_scale from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre
open private mean_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier

local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "pos" => Ioc (0 : ℝ) r₀
local notation "μ₊" => Measure.restrict (volume : Measure ℝ) pos
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "N" => fun n : Nat => ((n+2 : Nat) : ℝ)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "scale" => fun c (n : Nat) => (Real.log (N n) : ℂ)*phase c n
local notation "decay" => fun n : Nat => ((n+1 : Nat) : ℝ)^(-(1/2 : ℝ))
local notation "rho" => fun n : Nat => q/N n
local notation "delta" => fun c (n : Nat) => floorFromResponses c+riemannZeta (s₀ c) • elementarySource c-compensated c (n+2)
local notation "U" => fun c n => (scale c n)⁻¹ • delta c n
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "b" => fun c n => (scale c n)⁻¹*B c n

private theorem counted_input_even (c : BurnolCompletedMellinCoordinate) (n : Nat) : reflectL2 (U c n) = U c n := by
  change reflectL2 ((scale c n)⁻¹ • (_-compensated c (n+2))) = _
  rw [map_smul, map_sub, complete_even, compensated_even]

private theorem counted_input_parity (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, U c n (-x) = U c n x := by
  have reflected := Lp.coeFn_compMeasurePreserving (U c n) negMeasurePreserving
  change ∀ᵐ x : ℝ ∂volume, reflectL2 (U c n) x = U c n (-x) at reflected
  rw [counted_input_even] at reflected
  exact reflected.mono fun _ h => h.symm

private theorem rho_le_half (n : Nat) : rho n ≤ r₀ := by
  have lower : (2 : ℝ) ≤ N n := by
    change (2 : ℝ) ≤ ((n+2 : Nat) : ℝ)
    exact_mod_cast Nat.le_add_left 2 n
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) lower

private theorem normalized_settled_positive (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, 0 < x → x ≤ q → rho n < x → U c n x = b c n*seedRaw c.value x := by
  filter_upwards [actual_settled_count_difference c n, Lp.coeFn_smul (scale c n)⁻¹ (delta c n)]
    with x atx scaleRead positive inside covered
  have npos : 0 < N n := by positivity
  have settled : q/x < N n := (div_lt_iff₀ positive).mpr (by
    have paid := (div_lt_iff₀ npos).mp covered
    rwa [mul_comm] at paid)
  rw [scaleRead, Pi.smul_apply, smul_eq_mul, atx positive inside settled, mul_assoc]

private theorem uncovered_counted_input_mass (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ∫ x in Ioc (0 : ℝ) (rho n), ‖U c n x‖) atTop (𝓝 0) := by
  obtain ⟨budget, nonnegative, rate⟩ := actual_counted_source_tail_bound c
  let β := c.value.re
  have βpos : 0 < β := by dsimp only [β]; linarith [c.rightHalf]
  have indices : Tendsto (fun n : Nat => ((n+1 : Nat) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have nextIndices : Tendsto N atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have late : ∀ᶠ n : Nat in atTop, 1 ≤ Real.log (N n) :=
    (Real.tendsto_log_atTop.comp nextIndices).eventually (eventually_ge_atTop 1)
  let C := 2*budget*q^(1/2 : ℝ)
  have goes : Tendsto (fun n : Nat => C*((n+1 : Nat) : ℝ)^(β-1)) atTop (𝓝 0) := by
    have power := (tendsto_rpow_neg_atTop (sub_pos.mpr c.belowOne)).comp indices
    simpa only [neg_sub, Function.comp_def, mul_zero] using power.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg (fun _ => norm_nonneg _)) _ goes
  filter_upwards [late] with n clock
  let M : ℝ := (n+1 : Nat)
  have mpos : 0 < M := by dsimp only [M]; positivity
  have mN : M ≤ N n := by dsimp only [M]; exact_mod_cast Nat.le_succ (n+1)
  have npos := mpos.trans_le mN
  have double : N n ≤ 2*M := by dsimp only [M]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have radius : 0 ≤ rho n := by positivity
  have phaseNorm : ‖phase c n‖ = (N n)^(-β) := by
    change ‖((N n : ℝ) : ℂ)^(-s₀ c)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos npos, neg_re]
    simp only [β, star_def, conj_re]
  have scaleBound : ‖(scale c n)⁻¹‖ ≤ 2*M^β := by
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans clock), phaseNorm, mul_inv_rev,
      ← Real.rpow_neg npos.le, neg_neg]
    calc
      _ ≤ (N n)^β := mul_le_of_le_one_right (Real.rpow_nonneg npos.le _) (inv_le_one_of_one_le₀ clock)
      _ ≤ (2*M)^β := Real.rpow_le_rpow npos.le double βpos.le
      _ = (2 : ℝ)^β*M^β := Real.mul_rpow (by norm_num) mpos.le
      _ ≤ _ := by
        have two : (2 : ℝ)^β ≤ 2 := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) c.belowOne.le
        exact mul_le_mul_of_nonneg_right two (Real.rpow_nonneg mpos.le _)
  have mass : ‖U c n‖ ≤ (2*M^β)*(budget*decay n) := by
    rw [norm_smul]
    exact mul_le_mul scaleBound (rate n) (norm_nonneg _) (by positivity)
  have width : (rho n)^(1/2 : ℝ) ≤ q^(1/2 : ℝ)*decay n := by
    calc
      _ ≤ (q/M)^(1/2 : ℝ) := Real.rpow_le_rpow radius
        (div_le_div_of_nonneg_left (by norm_num) mpos mN) (by norm_num)
      _ = _ := by
        change (q/M)^(1/2 : ℝ) = q^(1/2 : ℝ)*M^(-(1/2 : ℝ))
        rw [Real.div_rpow (by norm_num) mpos.le, div_eq_mul_inv, Real.rpow_neg mpos.le]
  calc
    _ ≤ ‖U c n‖*(rho n)^(1/2 : ℝ) := positive_window_L1_bound (rho n) radius (U c n)
    _ ≤ ((2*M^β)*(budget*decay n))*(q^(1/2 : ℝ)*decay n) :=
      mul_le_mul mass width (Real.rpow_nonneg radius _) (by positivity)
    _ = C*(M^β*M^(-(1/2 : ℝ))*M^(-(1/2 : ℝ))) := by dsimp only [C, M]; ring
    _ = _ := by
      rw [← Real.rpow_add mpos, ← Real.rpow_add mpos, show β+-(1/2 : ℝ)+-(1/2 : ℝ) = β-1 by ring]

private theorem centre_norm_positive (v : BurnolL2) (even : ∀ᵐ x : ℝ ∂volume, v (-x) = v x) :
    ‖(splitAtPhysicalCutoff r₀ v).1‖ = 2*(∫ x in pos, ‖v x‖) := by
  let f := fun x : ℝ => ‖v x‖
  have ae := (even.mono fun _ h => congrArg norm h : ∀ᵐ x : ℝ ∂volume, f (-x) = f x)
  have input := (originalPhysicalCutoff_integrable r₀ v).norm
  have full : (fun x => ‖originalPhysicalCutoff r₀ v x‖) =ᵐ[volume] (symmetricInterval r₀).indicator f := by
    filter_upwards [originalPhysicalCutoff_coeFn r₀ v] with x h
    rw [h]
    by_cases member : x ∈ symmetricInterval r₀
    · rw [indicator_of_mem member, indicator_of_mem member]
    · rw [indicator_of_notMem member, indicator_of_notMem member, norm_zero]
  have positive : Integrable (Set.indicator pos f) volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact (input.congr full).integrableOn.congr_fun (fun x hx => indicator_of_mem
      (show x ∈ symmetricInterval r₀ from ⟨(by norm_num : (-r₀ : ℝ) ≤ 0).trans hx.1.le, hx.2⟩) _)
      measurableSet_Ioc
  have negative : Integrable (fun x : ℝ => Set.indicator pos f (-x)) volume :=
    negMeasurePreserving.integrable_comp_of_integrable positive
  change ‖(originalPhysicalCutoff_integrable r₀ v).toL1 (originalPhysicalCutoff r₀ v : ℝ → ℂ)‖ = _
  rw [L1.norm_of_fun_eq_integral_norm, integral_congr_ae full,
    integral_congr_ae (even_cut_reconstruction f ae)]
  have both : (∫ x, Set.indicator pos f x+Set.indicator pos f (-x)) =
      (∫ x, Set.indicator pos f x)+(∫ x, Set.indicator pos f (-x)) := by
    simpa only [Pi.add_apply] using integral_add positive negative
  rw [both, integral_neg_eq_self (Set.indicator pos f), ← two_mul, integral_indicator measurableSet_Ioc]

private theorem positive_counted_input_mass (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ∫ x in pos, ‖U c n x‖) atTop (𝓝 0) := by
  have seedWhole : IntegrableOn (seedRaw c.value) (symmetricInterval q) (volume : Measure ℝ) :=
    actual_seed_integrable c.value c.belowOne
  have seed : IntegrableOn (seedRaw c.value) pos (volume : Measure ℝ) := seedWhole.mono_set
    (fun x (h : x ∈ pos) => ⟨(by norm_num : (-q : ℝ) ≤ 0).trans h.1.le, h.2.trans (by norm_num)⟩)
  let constant : ℝ := ∫ x in pos, ‖seedRaw c.value x‖
  have covered := (count_below_log_scale c).norm.mul_const constant
  simp only [norm_zero, zero_mul] at covered
  have total := covered.add (uncovered_counted_input_mass c)
  simp only [add_zero] at total
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ total
  filter_upwards with n
  let f := fun x : ℝ => ‖U c n x‖
  have small := rho_le_half n
  have masked : Integrable f μ₊ := by
    have : IsFiniteMeasure μ₊ := ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩
    exact (((Lp.memLp (U c n)).mono_measure Measure.restrict_le_self).integrable (by norm_num)).norm
  have inside := masked.indicator (s := Ioc 0 (rho n)) measurableSet_Ioc
  have law : ∀ᵐ x : ℝ ∂μ₊, f x ≤ ‖b c n‖*‖seedRaw c.value x‖+
      (Ioc 0 (rho n)).indicator f x := by
    filter_upwards [ae_restrict_of_ae (normalized_settled_positive c n), ae_restrict_mem measurableSet_Ioc]
      with x settled atx
    by_cases covered : rho n < x
    · have outside : x ∉ Ioc 0 (rho n) := fun h => covered.not_ge h.2
      dsimp only [f]
      rw [settled atx.1 (atx.2.trans (by norm_num)) covered, norm_mul, indicator_of_notMem outside, add_zero]
    · have member : x ∈ Ioc 0 (rho n) := ⟨atx.1, le_of_not_gt covered⟩
      rw [indicator_of_mem member]
      exact le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have paid := integral_mono_ae masked ((seed.norm.const_mul ‖b c n‖).add inside) law
  change (∫ x in pos, f x) ≤ ∫ x in pos, ‖b c n‖*‖seedRaw c.value x‖+
    (Ioc 0 (rho n)).indicator f x at paid
  rw [integral_add (seed.norm.const_mul _) inside, integral_const_mul, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioc_right small)] at paid
  change (∫ x in pos, f x) ≤ ‖b c n‖*constant+∫ x in Ioc 0 (rho n), f x
  exact paid

private theorem normalized_input_compact (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    originalPhysicalCutoff q (U c n) = U c n := by
  change FiniteMobiusResolventFlux.cutoff q ((scale c n)⁻¹ • (_-compensated c (n+2))) = _
  rw [map_smul, map_sub]
  exact congrArg ((scale c n)⁻¹ • ·) (congrArg₂ (· - ·) (complete_compact c) (actual_compact c (n+2) (by omega)))

private theorem counted_input_exterior (c : BurnolCompletedMellinCoordinate) :
    ∃ column : BurnolL2, ∀ n : Nat, (splitAtPhysicalCutoff r₀ (U c n)).2 = b c n • column := by
  let power := (countedHomogeneousSplit c).2
  let boxq := FiniteMobiusResolventFlux.box q
  let boxr := FiniteMobiusResolventFlux.box r₀
  let mean := GapEuler.gapMean q c
  let edge := originalPhysicalCutoff q power
  let column := edge-mean • (boxq-boxr)
  refine ⟨column, fun n => ?_⟩
  have radius := rho_le_half n
  have seed (x : ℝ) : seedRaw c.value x = ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ)-mean := by
    unfold seedRaw
    rw [mul_sub, mean_power c, powerRaw]
    ring
  have settled : ∀ᵐ x : ℝ ∂volume, r₀ < |x| → |x| ≤ q → U c n x = b c n*seedRaw c.value x := by
    have positive := normalized_settled_positive c n
    filter_upwards [positive, negMeasurePreserving.quasiMeasurePreserving.ae positive,
      counted_input_parity c n] with x direct opposite parity live inside
    have nonzero : x ≠ 0 := abs_pos.mp ((by norm_num : 0 < r₀).trans live)
    rcases lt_or_gt_of_ne nonzero with negative | positiveX
    · have negX : 0 < -x := neg_pos.mpr negative
      change 0 < -x → -x ≤ q → rho n < -x → _ at opposite
      rw [abs_of_neg negative] at live inside
      rw [← parity, opposite negX inside (radius.trans_lt live), seed, seed, abs_neg]
    · rw [abs_of_pos positiveX] at live inside
      exact direct positiveX inside (radius.trans_lt live)
  have compact := originalPhysicalCutoff_coeFn q (U c n)
  rw [normalized_input_compact c n] at compact
  apply Lp.ext
  filter_upwards [cutoff_split_read r₀ (U c n), settled, compact, Lp.coeFn_smul (b c n) column,
    Lp.coeFn_sub edge (mean • (boxq-boxr)), Lp.coeFn_smul mean (boxq-boxr), Lp.coeFn_sub boxq boxr,
    originalPhysicalCutoff_coeFn q power, homogeneous_tail_read c,
    FiniteMobiusResolventFlux.box_read q, FiniteMobiusResolventFlux.box_read r₀]
    with x split act source scalar difference meanRead boxes edgeRead powerRead qRead rRead
  change column x = _ at difference
  change edge x = _ at edgeRead
  change power x = _ at powerRead
  change boxq x = _ at qRead
  change boxr x = _ at rRead
  rw [split.2, scalar, Pi.smul_apply, smul_eq_mul, difference, Pi.sub_apply,
    meanRead, Pi.smul_apply, smul_eq_mul, boxes, Pi.sub_apply, edgeRead, qRead, rRead]
  by_cases inside : x ∈ symmetricInterval r₀
  · have large : x ∈ symmetricInterval q := abs_le.mp ((abs_le.mpr inside).trans (by norm_num))
    rw [indicator_of_mem inside, sub_self, indicator_of_mem inside, indicator_of_mem large,
      indicator_of_mem large, powerRead, if_neg (not_lt_of_ge (abs_le.mpr inside)), sub_self, mul_zero, sub_self, mul_zero]
  · have outside : r₀ < |x| := lt_of_not_ge (fun h => inside (abs_le.mp h))
    rw [indicator_of_notMem inside, sub_zero, indicator_of_notMem inside]
    by_cases large : x ∈ symmetricInterval q
    · rw [indicator_of_mem large, indicator_of_mem large, powerRead, if_pos outside, sub_zero, mul_one,
        act outside (abs_le.mpr large), seed]
    · rw [indicator_of_notMem large, indicator_of_notMem large, sub_self, mul_zero, sub_self, mul_zero,
        source, indicator_of_notMem large]

/-- Both unweighted pieces of the same actual normalized input vanish strongly. -/
theorem actual_counted_unweighted_source_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => splitAtPhysicalCutoff r₀ (U c n)) atTop (𝓝 (0, 0)) := by
  apply Tendsto.prodMk_nhds
  · apply tendsto_zero_iff_norm_tendsto_zero.2
    have source := (positive_counted_input_mass c).const_mul (2 : ℝ)
    simp only [mul_zero] at source
    exact source.congr' (Eventually.of_forall fun n => (centre_norm_positive (U c n) (counted_input_parity c n)).symm)
  · obtain ⟨column, equation⟩ := counted_input_exterior c
    have source : Tendsto (fun n => b c n • column) atTop (𝓝 ((0 : ℂ) • column)) :=
      (count_below_log_scale c).smul tendsto_const_nhds
    rw [zero_smul] at source
    change Tendsto (fun n => (splitAtPhysicalCutoff r₀ (U c n)).2) atTop (𝓝 (0 : BurnolL2))
    exact source.congr' (Eventually.of_forall fun n => (equation n).symm)

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
