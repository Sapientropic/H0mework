import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow.Geometric
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.ClockReconstruction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow

open Complex Filter FourierTransform MeasureTheory Set
open scoped BigOperators Topology
open private damped_fourier_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers
open private shift denominator_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow.Geometric

local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation
local notation "w" => (3 / 8 : ℂ)

private def line (y : ℝ) : BurnolCompletedMellinCoordinate :=
  ⟨(3 / 4 : ℂ) + (↑(4 * Real.pi * y) : ℂ) * I,
    by norm_num [Complex.add_re, Complex.mul_re], by norm_num [Complex.add_re, Complex.mul_re]⟩

private theorem line_norm (y : ℝ) : ‖R (line y)‖ ≤ 8 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  let z := (line y).value / 2
  have re : z.re = 3 / 8 := by
    norm_num [z, line, Complex.div_re, Complex.add_re, Complex.mul_re]
  change ‖-(∫ t in Ioi (0 : ℝ), burnolDirectRightResolventIntegrand z v t)‖ ≤ _
  rw [norm_neg]
  refine (norm_integral_le_integral_norm _).trans ?_
  have kernel (t : ℝ) :
      ‖burnolDirectRightResolventIntegrand z v t‖ = Real.exp (-(1 / 8 : ℝ) * t) * ‖v‖ := by
    rw [burnolDirectRightResolventIntegrand, norm_smul, (D (-t / 2)).norm_map,
      norm_positiveMellinQuarterRightResolventWeight, re]
    norm_num
  simp_rw [kernel]
  rw [integral_mul_const, integral_exp_mul_Ioi (by norm_num : -(1 / 8 : ℝ) < 0)]
  norm_num

private theorem shift_continuous (c : BurnolCompletedMellinCoordinate) :
    Continuous (fun y : ℝ => shift c (line y)) := by
  unfold shift line
  fun_prop

private theorem ratio_continuous (c : BurnolCompletedMellinCoordinate) :
    Continuous (fun y : ℝ => ratio c (line y)) :=
  (shift_continuous c).div (continuous_const.add (shift_continuous c))
    (fun y => denominator_ne_zero c (line y))

private theorem weight_continuous (c : BurnolCompletedMellinCoordinate) (k j : ℕ) :
    Continuous (fun y : ℝ => weight c (line y) k j) := by
  unfold weight
  have ratioRead := ratio_continuous c
  fun_prop

private theorem finite_norm_band (c : BurnolCompletedMellinCoordinate) (W : ℝ) (width : 0 ≤ W) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ y ∈ Icc (-W) W, ‖ratio c (line y)‖ ≤ ρ := by
  have nonempty : (Icc (-W) W).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨y, _, highest⟩ := isCompact_Icc.exists_isMaxOn nonempty (ratio_continuous c).norm.continuousOn
  exact ⟨‖ratio c (line y)‖, norm_nonneg _, ratio_norm_lt_one c _, highest⟩

section Observe
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (Q : BurnolL2 →L[ℂ] E)
variable (test : SchwartzMap ℝ ℂ)

private def damped (v : BurnolL2) : ℝ → E :=
  (Ioi (0 : ℝ)).indicator (fun t => Q (burnolDirectRightResolventIntegrand w v t))

omit [CompleteSpace E] in
private theorem damped_integrable (v : BurnolL2) : Integrable (damped Q v) := by
  have source : IntegrableOn (fun t => Q (burnolDirectRightResolventIntegrand w v t)) (Ioi 0) :=
    Q.integrable_comp (burnolDirectRightResolventIntegrand_integrableOn w (by norm_num) v)
  exact source.integrable_indicator measurableSet_Ioi

private theorem frequency_read (v : BurnolL2) (y : ℝ) :
    𝓕 (damped Q v) y = -Q (R (line y) v) :=
  damped_fourier_read Q v y

/-- Average the actual inward dilation against the specified Fourier window. -/
def windowRead (v : BurnolL2) : E :=
  ∫ t in Ioi (0 : ℝ), 𝓕 (test : ℝ → ℂ) t • Q (burnolDirectRightResolventIntegrand w v t)

private theorem exact_window (v : BurnolL2) :
    windowRead Q test v = -(∫ y : ℝ, test y • Q (R (line y) v)) := by
  have swapped : (∫ t : ℝ, 𝓕 (test : ℝ → ℂ) t • damped Q v t) =
      ∫ y : ℝ, test y • 𝓕 (damped Q v) y := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner test.integrable (damped_integrable Q v))
  rw [windowRead, ← integral_indicator measurableSet_Ioi, ← integral_neg]
  calc
    _ = ∫ t : ℝ, 𝓕 (test : ℝ → ℂ) t • damped Q v t := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases inside : t ∈ Ioi (0 : ℝ)
      · simp only [damped, indicator_of_mem inside]
      · simp only [damped, indicator_of_notMem inside, smul_zero]
    _ = _ := by
      rw [swapped]
      simp_rw [frequency_read, smul_neg]

omit [CompleteSpace E] in
private theorem frequency_bound (v : BurnolL2) (y : ℝ) :
    ‖test y • Q (R (line y) v)‖ ≤ (8 * ‖Q‖ * ‖v‖) * ‖test y‖ := by
  rw [norm_smul]
  have rBound := ((R (line y)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (line_norm y) (norm_nonneg v))
  calc
    _ ≤ ‖test y‖ * (‖Q‖ * (8 * ‖v‖)) :=
      mul_le_mul_of_nonneg_left ((Q.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left rBound (norm_nonneg Q))) (norm_nonneg _)
    _ = _ := by ring

private theorem frequency_integrable (v : BurnolL2) :
    Integrable (fun y : ℝ => test y • Q (R (line y) v)) := by
  have cont : Continuous (fun y : ℝ => Q (R (line y) v)) := by
    have exact : (fun y : ℝ => Q (R (line y) v)) = fun y => -𝓕 (damped Q v) y := by
      funext y
      rw [frequency_read, neg_neg]
    rw [exact]
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (damped_integrable Q v)).neg
  exact (test.integrable.norm.const_mul (8 * ‖Q‖ * ‖v‖)).mono'
    (test.continuous.smul cont).aestronglyMeasurable (Eventually.of_forall (frequency_bound Q test v))

/-- The finite coefficient reads only the original parameter and the specified window. -/
def coefficient (c : BurnolCompletedMellinCoordinate) (W : ℝ) (k j : ℕ) : ℂ :=
  -(∫ y in Icc (-W) W, test y * weight c (line y) k j)

private theorem weight_integrable (c : BurnolCompletedMellinCoordinate) (W : ℝ) (k j : ℕ) :
    IntegrableOn (fun y : ℝ => test y * weight c (line y) k j) (Icc (-W) W) :=
  (test.continuous.mul (weight_continuous c k j)).continuousOn.integrableOn_compact isCompact_Icc

def finiteWindow (c : BurnolCompletedMellinCoordinate) (W : ℝ) (N : ℕ) (v : BurnolL2) : E :=
  ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1),
    coefficient test c W k j • Q ((R c ^ (j + 1)) v)

private theorem exact_finite_window (c : BurnolCompletedMellinCoordinate) (W : ℝ) (N : ℕ)
    (v : BurnolL2) :
    finiteWindow Q test c W N v =
      -(∫ y in Icc (-W) W, test y • Q (finiteResolvent c (line y) N v)) := by
  let μ := volume.restrict (Icc (-W) W)
  have integrable_term (k j : ℕ) :
      Integrable (fun y : ℝ => (test y * weight c (line y) k j) • Q ((R c ^ (j + 1)) v)) μ :=
    (weight_integrable test c W k j).smul_const _
  unfold finiteWindow finiteResolvent coefficient
  simp only [_root_.sum_apply, _root_.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  symm
  rw [integral_finsetSum, ← Finset.sum_neg_distrib]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum, ← Finset.sum_neg_distrib]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_smul_const, neg_smul]
    · exact fun j _ => integrable_term k j
  · exact fun k _ => integrable_finsetSum _ (fun j _ => integrable_term k j)

omit [CompleteSpace E] in
private theorem finite_frequency_integrable (c : BurnolCompletedMellinCoordinate) (W : ℝ) (N : ℕ)
    (v : BurnolL2) :
    IntegrableOn (fun y : ℝ => test y • Q (finiteResolvent c (line y) N v)) (Icc (-W) W) := by
  unfold finiteResolvent
  simp only [_root_.sum_apply, _root_.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro j _
  exact (weight_integrable test c W k j).smul_const _

/-- The same finite coefficients approximate the complete source action on every input. -/
theorem actual_finite_window_error (c : BurnolCompletedMellinCoordinate) (W : ℝ) (width : 0 ≤ W) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (N : ℕ) (v : BurnolL2),
      ‖windowRead Q test v - finiteWindow Q test c W N v‖ ≤
        8 * ‖Q‖ * ‖v‖ * ((∫ y in (Icc (-W) W)ᶜ, ‖test y‖) +
          ρ ^ N * ∫ y in Icc (-W) W, ‖test y‖) := by
  obtain ⟨ρ, nonnegative, strict, bandBound⟩ := finite_norm_band c W width
  refine ⟨ρ, nonnegative, strict, fun N v => ?_⟩
  let band := Icc (-W) W
  let f := fun y : ℝ => test y • Q (R (line y) v)
  let g := fun y : ℝ => test y • Q (finiteResolvent c (line y) N v)
  have fInt : Integrable f := frequency_integrable Q test v
  have gInt : IntegrableOn g band := finite_frequency_integrable Q test c W N v
  have split := integral_add_compl (s := band) measurableSet_Icc fInt
  have inside : (∫ y in band, f y - g y) = (∫ y in band, f y) - ∫ y in band, g y :=
    integral_sub fInt.integrableOn gInt
  have difference : windowRead Q test v - finiteWindow Q test c W N v =
      -((∫ y in band, f y - g y) + ∫ y in bandᶜ, f y) := by
    rw [exact_window, exact_finite_window]
    change -(∫ y, f y) - (-(∫ y in band, g y)) = _
    rw [← split, inside]
    abel
  let K := 8 * ‖Q‖ * ‖v‖
  have tail : ‖∫ y in bandᶜ, f y‖ ≤ K * ∫ y in bandᶜ, ‖test y‖ := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (test.integrable.norm.const_mul K).integrableOn
      (Eventually.of_forall (frequency_bound Q test v))
  have middle : ‖∫ y in band, f y - g y‖ ≤ K * ρ ^ N * ∫ y in band, ‖test y‖ := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (test.integrable.norm.const_mul (K * ρ ^ N)).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y inBand
    dsimp only [f, g, K]
    rw [← smul_sub, ← map_sub, norm_smul]
    have rBound := actual_resolvent_remainder_bound c (line y) N v
    have qBound := Q.le_opNorm (R (line y) v - finiteResolvent c (line y) N v)
    have power : ‖ratio c (line y)‖ ^ N ≤ ρ ^ N :=
      pow_le_pow_left₀ (norm_nonneg _) (bandBound y inBand) N
    calc
      _ ≤ ‖test y‖ * (‖Q‖ * (‖R (line y)‖ * ‖ratio c (line y)‖ ^ N * ‖v‖)) :=
        mul_le_mul_of_nonneg_left (qBound.trans (mul_le_mul_of_nonneg_left rBound (norm_nonneg Q))) (norm_nonneg _)
      _ ≤ ‖test y‖ * (‖Q‖ * (8 * ρ ^ N * ‖v‖)) := by gcongr; exact line_norm y
      _ = _ := by ring
  rw [difference, norm_neg]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add middle tail
    _ = _ := by dsimp only [K, band]; ring

private theorem frequency_tail_tendsto :
    Tendsto (fun W : ℕ => ∫ y in (Icc (-(W : ℝ)) (W : ℝ))ᶜ, ‖test y‖) atTop (𝓝 0) := by
  let tails (W : ℕ) := (Icc (-(W : ℝ)) (W : ℝ))ᶜ
  have nested : Antitone tails := by
    intro i j before
    have order : (i : ℝ) ≤ j := Nat.cast_le.mpr before
    exact Set.compl_subset_compl.mpr (Icc_subset_Icc (neg_le_neg order) order)
  have empty : (⋂ W, tails W) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y all
    obtain ⟨W, inside⟩ := exists_nat_gt |y|
    exact (Set.mem_iInter.mp all W) (abs_le.mp inside.le)
  have mass := tendsto_setIntegral_of_antitone (μ := volume) (f := fun y : ℝ => ‖test y‖)
    (s := tails) (fun _ => measurableSet_Icc.compl) nested ⟨0, test.integrable.norm.integrableOn⟩
  rw [empty, setIntegral_empty] at mass
  exact mass

/-- One finite budget chosen from the window works on the entire ambient source. -/
theorem actual_finite_window_precise (c : BurnolCompletedMellinCoordinate) (ε : ℝ) (positive : 0 < ε) :
    ∃ W N : ℕ, ∀ v : BurnolL2,
      ‖windowRead Q test v - finiteWindow Q test c W N v‖ ≤ 8 * ‖Q‖ * ‖v‖ * ε := by
  have half := half_pos positive
  obtain ⟨W, outside⟩ := ((frequency_tail_tendsto test).eventually (Iio_mem_nhds half)).exists
  obtain ⟨ρ, nonnegative, strict, paid⟩ := actual_finite_window_error Q test c W (Nat.cast_nonneg W)
  have decays := (tendsto_pow_atTop_nhds_zero_of_lt_one nonnegative strict).mul_const
    (∫ y in Icc (-(W : ℝ)) (W : ℝ), ‖test y‖)
  rw [zero_mul] at decays
  obtain ⟨N, inside⟩ := (decays.eventually (Iio_mem_nhds half)).exists
  refine ⟨W, N, fun v => (paid N v).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change (∫ y in (Icc (-(W : ℝ)) (W : ℝ))ᶜ, ‖test y‖) < ε / 2 at outside
  change ρ ^ N * (∫ y in Icc (-(W : ℝ)) (W : ℝ), ‖test y‖) < ε / 2 at inside
  linarith

end Observe
end OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.OutsideHistory

open BurnolPhysicalState SourceGeneratedActionObservationHistory MeasureTheory Set
open OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow
open scoped BigOperators
open private successor_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.Kernel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "A" => sourceStep observation nontrivial half
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

/-- Use precisely the emitted outside coordinates 1 through N of the original history. -/
def recordedWindow (test : SchwartzMap ℝ ℂ) (W : ℝ) (N : ℕ)
    (history : completion A outsideRead) : BurnolL2 :=
  ∑ k : Fin N, ∑ j : Fin (k.val + 1),
    coefficient test c W k.val j.val • stageRead A outsideRead N history
      ⟨j.val + 1, Nat.succ_lt_succ (lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) k.isLt)⟩

private theorem recorded_window_source (test : SchwartzMap ℝ ℂ) (W : ℝ) (N : ℕ)
    (pair : SourcePair) :
    recordedWindow observation nontrivial half test W N (sourceMap A outsideRead pair) =
      finiteWindow O test c W N (Inv.pairTotal pair) := by
  simp only [recordedWindow, source_reads_stage, successor_read, finiteWindow]
  let read (k j : ℕ) := coefficient test c W k j •
    O ((burnolDirectRightResolventCLM c ^ (j+1)) (Inv.pairTotal pair))
  change (∑ k : Fin N, ∑ j : Fin (k.val+1), read k.val j.val) =
    ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k+1), read k j
  have each (k : Fin N) :
      (∑ j : Fin (k.val+1), read k.val j.val) =
        ∑ j ∈ Finset.range (k.val+1), read k.val j :=
    Fin.sum_univ_eq_sum_range _ _
  simp_rw [each]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => ∑ j ∈ Finset.range (k+1), read k j) N

variable (depth : ℕ)
local notation "source" => D.input observation nontrivial half depth

theorem actual_recorded_window_error (test : SchwartzMap ℝ ℂ) (W : ℝ) (width : 0 ≤ W) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (N ordinal : ℕ),
      ‖windowRead O test (Inv.pairTotal (source ordinal)) -
        recordedWindow observation nontrivial half test W N (sourceMap A outsideRead (source ordinal))‖ ≤
        8 * ‖O‖ * ‖Inv.pairTotal (source ordinal)‖ * ((∫ y in (Icc (-W) W)ᶜ, ‖test y‖) +
          ρ ^ N * ∫ y in Icc (-W) W, ‖test y‖) := by
  obtain ⟨ρ, nonnegative, strict, bound⟩ := actual_finite_window_error O test c W width
  refine ⟨ρ, nonnegative, strict, fun N ordinal => ?_⟩
  rw [recorded_window_source]
  exact bound N (Inv.pairTotal (source ordinal))

/-- The same finite budget consumes each original Division's own recorded prefix. -/
theorem actual_recorded_window_precise (test : SchwartzMap ℝ ℂ) (ε : ℝ) (positive : 0 < ε) :
    ∃ W N : ℕ, ∀ ordinal : ℕ,
      ‖windowRead O test (Inv.pairTotal (source ordinal)) -
        recordedWindow observation nontrivial half test W N (sourceMap A outsideRead (source ordinal))‖ ≤
        8 * ‖O‖ * ‖Inv.pairTotal (source ordinal)‖ * ε := by
  obtain ⟨W, N, bound⟩ := actual_finite_window_precise O test c ε positive
  refine ⟨W, N, fun ordinal => ?_⟩
  rw [recorded_window_source]
  exact bound (Inv.pairTotal (source ordinal))

end OriginalKCofinalFullBranchFibre.OutsideHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
