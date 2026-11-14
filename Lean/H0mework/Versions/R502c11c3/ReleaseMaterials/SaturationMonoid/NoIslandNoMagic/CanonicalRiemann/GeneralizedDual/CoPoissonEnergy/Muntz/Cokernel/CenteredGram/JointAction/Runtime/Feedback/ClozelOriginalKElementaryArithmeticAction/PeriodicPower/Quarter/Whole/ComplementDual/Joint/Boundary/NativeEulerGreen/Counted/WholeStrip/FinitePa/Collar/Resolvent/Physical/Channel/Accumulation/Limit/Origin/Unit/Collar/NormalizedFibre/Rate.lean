import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.TailRate
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Exterior

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology ENNReal

open private reverse_resolvent from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent

local notation "q₀" => (1/4 : ℝ)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "ζ" => fun c => riemannZeta (s₀ c)
local notation "Z" => fun c => FiniteForcing.coefficient (s₀ c)
local notation "R₀" => fun c => burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
local notation "whole" => fun c => floorFromResponses c+ζ c • elementarySource c
local notation "delta" => fun c (n : Nat) => whole c-compensated c (n+2)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "decay" => fun n : Nat => ((n+1 : Nat) : ℝ)^(-(1/2 : ℝ))

private theorem compensation_bound (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ‖ζ c-Z c (n+2)‖ ≤ (|cutoffJetBudget c 0|+1/2)*decay n := by
  let M : ℝ := (n+1 : Nat)
  let N : ℝ := (n+2 : Nat)
  have mpos : 0 < M := by dsimp only [M]; positivity
  have mN : M ≤ N := by
    dsimp only [M, N]
    exact_mod_cast Nat.le_succ (n+1)
  have N1 : 1 ≤ N := by dsimp only [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n+1))
  have npos := mpos.trans_le mN
  have right : 1/2 < (s₀ c).re := by
    simpa only [star_def, conj_re] using c.rightHalf
  have power (exponent : ℝ) (small : exponent ≤ -(1/2 : ℝ)) :
      N^exponent ≤ decay n :=
    (Real.rpow_le_rpow_of_exponent_le N1 small).trans
      (Real.rpow_le_rpow_of_nonpos mpos mN (by norm_num))
  have data := actual_cutoff_jet_error c 0 (n+1)
  simp only [CoefficientJet.jet, CoefficientJet.zetaJet, iteratedDeriv_zero, CoefficientJet.finite,
    pow_zero, mul_one] at data
  change ‖Z c (n+2)-ζ c+(1/2 : ℂ)*phase c n‖ ≤ _ at data
  have phaseNorm : ‖phase c n‖ ≤ decay n := by
    change ‖(N : ℂ)^(-s₀ c)‖ ≤ _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos npos, neg_re]
    exact power _ (by linarith)
  have error : ‖Z c (n+2)-ζ c+(1/2 : ℂ)*phase c n‖ ≤ |cutoffJetBudget c 0| * decay n := by
    refine data.trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg npos.le _)).trans ?_)
    exact mul_le_mul_of_nonneg_left (power _ (by linarith)) (abs_nonneg _)
  have halfNorm : ‖(1/2 : ℂ)‖ = 1/2 := by rw [norm_div, norm_one]; norm_num
  calc
    ‖ζ c-Z c (n+2)‖ = ‖(Z c (n+2)-ζ c+(1/2 : ℂ)*phase c n)-(1/2 : ℂ)*phase c n‖ := by
      rw [norm_sub_rev (ζ c) (Z c (n+2)), add_sub_cancel_right]
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul, halfNorm, add_mul]
      exact add_le_add error (mul_le_mul_of_nonneg_left phaseNorm (by norm_num))

/-- The same complete-minus-compensated R field has a cutoff tail bound from
the original input's Euler velocity and the original Unit compensation. -/
theorem actual_counted_R_tail_bound (c : BurnolCompletedMellinCoordinate) :
    ∃ budget : ℝ, 0 ≤ budget ∧ ∀ n : Nat, ‖R₀ c (delta c n)‖ ≤ budget*decay n := by
  let input := OriginalCanonicalNativeEulerGreen.Counted.input c
  let cost := ‖(s₀ c) • R₀ c input+(2 : ℂ) • input‖
  obtain ⟨limit, converges, rate⟩ := CountedJointStrong.actual_resolvent_reverse_tail
    (OriginalPrimitiveRankBalance.conjugateCoordinate c) input
  have commute (N : Nat) :
      DualSource.source N (R₀ c input) = R₀ c (DualSource.source N input) :=
    reverse_resolvent N c input
  have actual : Tendsto (fun N => DualSource.source N (R₀ c input)) atTop
      (𝓝 (R₀ c (floorFromResponses c))) :=
    (((R₀ c).continuous.tendsto (floorFromResponses c)).comp (actual_floor_tendsto c)).congr'
      (Eventually.of_forall fun N => (commute N).symm)
  have source := tendsto_nhds_unique converges actual
  let unitCost := (|cutoffJetBudget c 0|+1/2)*‖R₀ c (elementarySource c)‖
  refine ⟨2*cost+unitCost, by dsimp only [cost, unitCost]; positivity, fun n => ?_⟩
  have initial := rate (n+1) (by omega)
  rw [source, commute] at initial
  change ‖R₀ c (floorFromResponses c)-R₀ c (DualSource.source (n+2) input)‖ ≤
    (2*decay n)*cost at initial
  have action : R₀ c (delta c n) =
      (R₀ c (floorFromResponses c)-R₀ c (DualSource.source (n+2) input))+
        (ζ c-Z c (n+2)) • R₀ c (elementarySource c) := by
    change R₀ c (floorFromResponses c+ζ c • elementarySource c-compensated c (n+2)) = _
    unfold compensated
    rw [map_sub, map_add, map_add, map_smul, map_smul]
    dsimp only [input]
    module
  have unit : ‖(ζ c-Z c (n+2)) • R₀ c (elementarySource c)‖ ≤ unitCost*decay n := by
    rw [norm_smul]
    apply (mul_le_mul_of_nonneg_right (compensation_bound c n) (norm_nonneg _)).trans_eq
    dsimp only [unitCost]
    ring
  rw [action]
  apply (norm_add_le _ _).trans ((add_le_add initial unit).trans_eq ?_)
  ring

private theorem positive_window_L1_bound (radius : ℝ) (nonnegative : 0 ≤ radius)
    (field : BurnolL2) :
    (∫ x in Ioc 0 radius, ‖field x‖) ≤ ‖field‖*radius^(1/2 : ℝ) := by
  let μ := volume.restrict (Ioc 0 radius)
  have measured : AEStronglyMeasurable (field : ℝ → ℂ) μ :=
    (Lp.aestronglyMeasurable field).mono_measure Measure.restrict_le_self
  have window : μ univ = ENNReal.ofReal radius := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have holder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := 1) (q := 2) (by norm_num) measured
  have exponent : 1/(1 : ℝ≥0∞).toReal - 1/(2 : ℝ≥0∞).toReal = (1/2 : ℝ) := by norm_num
  rw [exponent] at holder
  have restricted : eLpNorm (field : ℝ → ℂ) 2 μ ≤ eLpNorm (field : ℝ → ℂ) 2 volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have finite : eLpNorm (field : ℝ → ℂ) 2 volume * μ univ ^ (1/2 : ℝ) ≠ ∞ := by
    apply ENNReal.mul_ne_top (Lp.eLpNorm_ne_top field)
    rw [window]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  have comparison : eLpNorm (field : ℝ → ℂ) 1 μ ≤
      eLpNorm (field : ℝ → ℂ) 2 volume * μ univ ^ (1/2 : ℝ) :=
    holder.trans (by gcongr)
  have actual := ENNReal.toReal_mono finite comparison
  rw [toReal_eLpNorm measured, lpNorm_one_eq_integral_norm measured,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, window, ENNReal.toReal_ofReal nonnegative] at actual
  exact actual

/-- The original count's uncovered origin window loses its normalized L¹ mass
even though the complete normalized L² norm escapes. -/
theorem actual_normalized_counted_uncovered_L1 (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat =>
      ∫ x in Ioc (0 : ℝ) (q₀/((n+2 : Nat) : ℝ)), ‖countedNormalizedField c n x‖) atTop (𝓝 0) := by
  obtain ⟨budget, nonnegative, rate⟩ := actual_counted_R_tail_bound c
  let β := c.value.re
  have βpos : 0 < β := by dsimp only [β]; linarith [c.rightHalf]
  have indices : Tendsto (fun n : Nat => ((n+1 : Nat) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have nextIndices : Tendsto (fun n : Nat => ((n+2 : Nat) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have late : ∀ᶠ n : Nat in atTop, 1 ≤ Real.log ((n+2 : Nat) : ℝ) :=
    (Real.tendsto_log_atTop.comp nextIndices).eventually (eventually_ge_atTop 1)
  let C := 2*budget*q₀^(1/2 : ℝ)
  have goes : Tendsto (fun n : Nat => C*((n+1 : Nat) : ℝ)^(β-1)) atTop (𝓝 0) := by
    have power := (tendsto_rpow_neg_atTop (sub_pos.mpr c.belowOne)).comp indices
    simpa only [neg_sub, Function.comp_def, mul_zero] using power.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg (fun _ => norm_nonneg _)) _ goes
  filter_upwards [late] with n clock
  let M : ℝ := (n+1 : Nat)
  let N : ℝ := (n+2 : Nat)
  have mpos : 0 < M := by dsimp only [M]; positivity
  have mN : M ≤ N := by dsimp only [M, N]; exact_mod_cast Nat.le_succ (n+1)
  have npos := mpos.trans_le mN
  have double : N ≤ 2*M := by dsimp only [M, N]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have radius : 0 ≤ q₀/N := by positivity
  have phaseNorm : ‖phase c n‖ = N^(-β) := by
    change ‖(N : ℂ)^(-s₀ c)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos npos, neg_re]
    simp only [β, star_def, conj_re]
  have scale : ‖(((Real.log N : ℂ)*phase c n)⁻¹)‖ ≤ 2*M^β := by
    change 1 ≤ Real.log N at clock
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans clock), phaseNorm, mul_inv_rev,
      ← Real.rpow_neg npos.le, neg_neg]
    calc
      _ ≤ N^β := mul_le_of_le_one_right (Real.rpow_nonneg npos.le _) (inv_le_one_of_one_le₀ clock)
      _ ≤ (2*M)^β := Real.rpow_le_rpow npos.le double βpos.le
      _ = (2 : ℝ)^β*M^β := Real.mul_rpow (by norm_num) mpos.le
      _ ≤ _ := by
        have two : (2 : ℝ)^β ≤ 2 := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) c.belowOne.le
        exact mul_le_mul_of_nonneg_right two (Real.rpow_nonneg mpos.le _)
  have mass : ‖countedNormalizedField c n‖ ≤ (2*M^β)*(budget*decay n) := by
    rw [countedNormalizedField, norm_smul]
    exact mul_le_mul scale (rate n) (norm_nonneg _) (by positivity)
  have width : (q₀/N)^(1/2 : ℝ) ≤ q₀^(1/2 : ℝ)*decay n := by
    calc
      _ ≤ (q₀/M)^(1/2 : ℝ) := Real.rpow_le_rpow radius
        (div_le_div_of_nonneg_left (by norm_num) mpos mN) (by norm_num)
      _ = _ := by
        change (q₀/M)^(1/2 : ℝ) = q₀^(1/2 : ℝ)*M^(-(1/2 : ℝ))
        rw [Real.div_rpow (by norm_num) mpos.le, div_eq_mul_inv, Real.rpow_neg mpos.le]
  calc
    _ ≤ ‖countedNormalizedField c n‖*(q₀/N)^(1/2 : ℝ) :=
      positive_window_L1_bound (q₀/N) radius (countedNormalizedField c n)
    _ ≤ ((2*M^β)*(budget*decay n))*(q₀^(1/2 : ℝ)*decay n) :=
      mul_le_mul mass width (Real.rpow_nonneg radius _) (by positivity)
    _ = C*(M^β*M^(-(1/2 : ℝ))*M^(-(1/2 : ℝ))) := by
      dsimp only [C, M]
      ring
    _ = _ := by
      rw [← Real.rpow_add mpos, ← Real.rpow_add mpos, show β+-(1/2 : ℝ)+-(1/2 : ℝ) = β-1 by ring]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
