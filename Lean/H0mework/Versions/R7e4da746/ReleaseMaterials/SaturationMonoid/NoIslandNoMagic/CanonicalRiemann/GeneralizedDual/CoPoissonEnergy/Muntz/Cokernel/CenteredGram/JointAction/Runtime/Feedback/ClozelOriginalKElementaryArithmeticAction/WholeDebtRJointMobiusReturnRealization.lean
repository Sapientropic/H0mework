import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnAnnulusSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusReturnSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators ContDiff ArithmeticFunction
open private actual_fourier_next action_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTateRSource
open private fourier_c1 inverse_bounds positive_c1 from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusAnnulusSource
open private coordinate_eq forward_zero_window from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusUnitSource
open private forward_cut from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusProgrammeSource
open private adjoint_volterra adjoint_evenPart adjoint_fourier_eq_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open private conjugateCoordinate_twice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coord" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "w" => T.updatedWave observation nontrivial half

open private raw_gap raw_zero row_bounds row_weight_c1 row_slope_continuous row_derivative from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnAnnulusSource
def rowRaw (n : ℕ+) (x : ℝ) : ℂ :=
  if lower n < (4 : ℝ) then rowWeight observation nontrivial half n (|x|⁻¹) *
    burnolReciprocalStepSourceRaw q (lower n)⁻¹ x else 0

/-- The all-axis inverse is computed before the actual compact/outside source split. -/
def fullSourceRaw : ℝ → ℂ := burnolCenteredMobiusInverse (valueRaw observation nontrivial half)

def sourceRaw : ℝ → ℂ := (symmetricInterval (4 : ℝ)).indicator (fullSourceRaw observation nontrivial half)

def outsideSourceRaw : ℝ → ℂ := (symmetricInterval (4 : ℝ))ᶜ.indicator (fullSourceRaw observation nontrivial half)

def sourceMean : ℂ := ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * sourceRaw observation nontrivial half u

def responseRaw (x : ℝ) : ℂ := burnolInnerGapForward (outsideSourceRaw observation nontrivial half) x +
  contact observation nontrivial half + sourceMean observation nontrivial half

private theorem outer_measurable : Measurable (outerProfile observation nontrivial half) := by
  have power : Measurable (T.powerRaw coord) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (Complex.continuousAt_ofReal_cpow_const |x| ((coord).value - 1)
      (Or.inr (abs_ne_zero.mpr outside))).comp continuous_abs.continuousAt |>.continuousWithinAt
  unfold outerProfile
  exact (measurable_const.mul power).sub
    (((fourier_c1 (second observation nontrivial half : Hq)).continuous.measurable.add
      ((fourier_c1 (second observation nontrivial half : Hq)).continuous.measurable.comp (by fun_prop))).div_const 2)

private theorem row_weight_measurable (n : ℕ+) : Measurable (rowWeight observation nontrivial half n) := by
  unfold rowWeight
  exact (by fun_prop : Measurable (fun x : ℝ => (x : ℂ)⁻¹)).mul
    (((outer_measurable observation nontrivial half).comp (by fun_prop)).sub measurable_const)

private theorem row_raw_read (n : ℕ+) :
    (rowSource observation nontrivial half n : ℝ → ℂ) =ᵐ[volume] rowRaw observation nontrivial half n := by
  unfold rowSource rowRaw
  by_cases ordered : lower n < (4 : ℝ)
  · simp_rw [if_pos ordered]
    have invOrder : q ≤ (lower n)⁻¹ := by
      simpa only [show (4 : ℝ)⁻¹ = q by norm_num] using
        (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) (row_bounds n).2).mpr ordered.le
    have regular : ContinuousOn (rowWeight observation nontrivial half n) (Icc q (lower n)⁻¹) :=
      (row_weight_c1 observation nontrivial half n).continuousOn.mono
        (fun _ inside => (show (0 : ℝ) < q by norm_num).trans_le inside.1)
    obtain ⟨bound, bounded⟩ := (isCompact_Icc : IsCompact (Icc q (lower n)⁻¹)).exists_bound_of_continuousOn regular
    let raw := fun x : ℝ => rowWeight observation nontrivial half n (|x|⁻¹) *
      burnolReciprocalStepSourceRaw q (lower n)⁻¹ x
    have native : MemLp raw 2 volume := by
      apply (burnolReciprocalStepSource_memLp _ _ (by norm_num : (0 : ℝ) < q) invOrder).of_le_mul
        (c := bound) ((((row_weight_measurable observation nontrivial half n).comp (by fun_prop)).mul
          (burnolReciprocalStepSource_measurable _ _)).aestronglyMeasurable)
      filter_upwards with x
      change ‖rowWeight observation nontrivial half n (|x|⁻¹) * burnolReciprocalStepSourceRaw _ _ x‖ ≤ _
      rw [norm_mul]
      by_cases active : q ≤ |x|⁻¹ ∧ |x|⁻¹ < (lower n)⁻¹
      · exact mul_le_mul_of_nonneg_right (bounded _ ⟨active.1, active.2.le⟩) (norm_nonneg _)
      · simp only [burnolReciprocalStepSourceRaw, if_neg active, norm_zero, mul_zero, le_refl]
    have same : burnolWeightedReciprocalStepSource q (lower n)⁻¹
        (rowWeight observation nontrivial half n) (rowSlope observation nontrivial half n) = native.toLp raw := by
      apply ext_inner_left ℂ
      intro test
      rw [burnolWeightedReciprocalStepSource_pairing _ _ _ _ (by norm_num : (0 : ℝ) < q) invOrder
        (row_derivative observation nontrivial half n)
        (row_slope_continuous observation nontrivial half n ordered).continuousOn
        (row_slope_continuous observation nontrivial half n ordered).measurable, L2.inner_def]
      exact integral_congr_ae (native.coeFn_toLp.symm.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
    rw [same]
    exact native.coeFn_toLp
  · rw [if_neg ordered]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x zero
    simpa only [if_neg ordered, Pi.zero_apply] using zero

private theorem row_interval_read (n : ℕ+) (x : ℝ) :
    rowRaw observation nontrivial half n x = if lower n < |x| ∧ |x| ≤ (4 : ℝ) then
      outerProfile observation nontrivial half (|x| / (n : ℕ)) - contact observation nontrivial half else 0 := by
  by_cases ordered : lower n < (4 : ℝ)
  · rw [rowRaw, if_pos ordered]
    by_cases zero : x = 0
    · subst x
      simp only [abs_zero, inv_zero, burnolReciprocalStepSourceRaw,
        not_le.mpr (by norm_num : (0 : ℝ) < q), false_and, if_false, mul_zero,
        not_lt.mpr (row_bounds n).2.le]
    · have xp := abs_pos.mpr zero
      have incidence : q ≤ |x|⁻¹ ∧ |x|⁻¹ < (lower n)⁻¹ ↔ lower n < |x| ∧ |x| ≤ (4 : ℝ) := by
        rw [show q = (4 : ℝ)⁻¹ by norm_num]
        rw [inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) xp, inv_lt_inv₀ xp (row_bounds n).2, and_comm]
      unfold burnolReciprocalStepSourceRaw
      simp only [incidence]
      split_ifs with active
      · unfold rowWeight
        simp only [inv_inv, Complex.ofReal_inv]
        field_simp [Complex.ofReal_ne_zero.mpr xp.ne']
      · exact mul_zero _
  · have inactive : ¬(lower n < |x| ∧ |x| ≤ (4 : ℝ)) := fun active => ordered (active.1.trans_le active.2)
    rw [rowRaw, if_neg ordered, if_neg inactive]

private theorem row_window_read (n : ℕ+) (x : ℝ) :
    rowRaw observation nontrivial half n x = (symmetricInterval (4 : ℝ)).indicator
      (fun x => valueRaw observation nontrivial half (x / (n : ℕ)) - contact observation nontrivial half) x := by
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have one : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
  rw [row_interval_read]
  by_cases inside : |x| ≤ (4 : ℝ)
  · rw [indicator_of_mem (show x ∈ symmetricInterval (4 : ℝ) from abs_le.mp inside)]
    have scaled : |x / (n : ℕ)| ≤ (4 : ℝ) := by
      rw [abs_div, abs_of_pos np, div_le_iff₀ np]
      nlinarith
    rw [actual_window_profile observation nontrivial half scaled, abs_div, abs_of_pos np]
    by_cases small : |x| ≤ lower n
    · have smallDiv : |x| / (n : ℕ) ≤ q := (div_le_iff₀ np).mpr (by simpa only [lower, mul_comm] using small)
      rw [if_pos smallDiv, sub_self, if_neg (fun active => not_lt_of_ge small active.1)]
    · have largeDiv : ¬ |x| / (n : ℕ) ≤ q := by
        intro h
        apply small
        simpa only [lower, mul_comm] using (div_le_iff₀ np).mp h
      rw [if_neg largeDiv, if_pos ⟨lt_of_not_ge small, inside⟩]
  · rw [indicator_of_notMem (show x ∉ symmetricInterval (4 : ℝ) from fun h => inside (abs_le.mpr h)), if_neg (fun active => inside active.2)]

private theorem full_gap {x : ℝ} (inside : |x| ≤ q) : fullSourceRaw observation nontrivial half x = 0 :=
  burnolCenteredMobiusInverse_eq_zero_of_quarterGap _ (raw_gap observation nontrivial half) inside

theorem actual_full_inverse_action (x : ℝ) :
    burnolInnerGapForward (fullSourceRaw observation nontrivial half) x =
      valueRaw observation nontrivial half x - contact observation nontrivial half := by
  exact (burnolCenteredMobiusInverse_exactReconstruction _ (raw_gap observation nontrivial half) x).trans
    (by rw [raw_zero])

private theorem source_sum_read (x : ℝ) : sourceRaw observation nontrivial half x =
    ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
      FiniteMobiusResolventFlux.coefficient n * rowRaw observation nontrivial half n x := by
  unfold sourceRaw
  by_cases inside : x ∈ symmetricInterval (4 : ℝ)
  · rw [indicator_of_mem inside, fullSourceRaw,
      burnolMobiusFixedWindow_sum _ (raw_gap observation nontrivial half) x (abs_le.mpr inside)]
    apply Finset.sum_congr rfl
    intro n _
    rw [row_window_read, indicator_of_mem inside]
    simp only [burnolCenteredMobiusSummand, FiniteMobiusResolventFlux.coefficient, raw_zero]
    ring
  · rw [indicator_of_notMem inside]
    symm
    apply Finset.sum_eq_zero
    intro n _
    rw [row_window_read, indicator_of_notMem inside, mul_zero]

theorem actual_source_raw : (inverseSource observation nontrivial half : ℝ → ℂ) =ᵐ[volume]
    sourceRaw observation nontrivial half := by
  have rows : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ+ // n ∈ burnolCenteredMobiusCutoffFinset 4},
      (FiniteMobiusResolventFlux.coefficient n.1 • rowSource observation nontrivial half n.1 : BurnolL2) x =
        FiniteMobiusResolventFlux.coefficient n.1 * rowRaw observation nontrivial half n.1 x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_smul (FiniteMobiusResolventFlux.coefficient n.1)
      (rowSource observation nontrivial half n.1), row_raw_read observation nontrivial half n.1] with x scalar raw
    rw [scalar]
    change FiniteMobiusResolventFlux.coefficient n.1 * rowSource observation nontrivial half n.1 x = _
    rw [raw]
  filter_upwards [Lp.coeFn_fun_finsetSum (burnolCenteredMobiusCutoffFinset 4)
    (fun n => FiniteMobiusResolventFlux.coefficient n • rowSource observation nontrivial half n), rows] with x sum source
  rw [show inverseSource observation nontrivial half x = _ from sum, source_sum_read]
  exact Finset.sum_congr rfl (fun n slot => source ⟨n, slot⟩)

theorem actual_inverse_source : inverseSource observation nontrivial half =
    burnolMobiusSourceL2 (value observation nontrivial half) := by
  have valueRep : (value observation nontrivial half : BurnolL2) =ᵐ[volume]
      fun x => burnolInnerGapForward (fullSourceRaw observation nontrivial half) x - (-contact observation nontrivial half) := by
    filter_upwards [actual_value_raw observation nontrivial half] with x actual
    rw [actual, actual_full_inverse_action]
    ring
  have read := burnolMobiusSourceL2_forward_raw _ (full_gap observation nontrivial half)
    (-contact observation nontrivial half) (value observation nontrivial half) valueRep
  exact Lp.ext ((actual_source_raw observation nontrivial half).trans read.symm)

private theorem compact_gap {x : ℝ} (inside : |x| ≤ q) : sourceRaw observation nontrivial half x = 0 := by
  rw [sourceRaw, indicator_of_mem (show x ∈ symmetricInterval (4 : ℝ) from abs_le.mp (by linarith : |x| ≤ (4 : ℝ))), full_gap observation nontrivial half inside]

private theorem outside_gap {x : ℝ} (inside : |x| ≤ q) : outsideSourceRaw observation nontrivial half x = 0 := by
  exact indicator_of_notMem (not_not.mpr (abs_le.mp (by linarith : |x| ≤ (4 : ℝ)))) _

theorem actual_full_source_split (x : ℝ) : fullSourceRaw observation nontrivial half x =
    sourceRaw observation nontrivial half x + outsideSourceRaw observation nontrivial half x := by
  unfold sourceRaw outsideSourceRaw
  by_cases inside : x ∈ symmetricInterval (4 : ℝ)
  · rw [indicator_of_mem inside, indicator_of_notMem (not_not.mpr inside), add_zero]
  · rw [indicator_of_notMem inside, indicator_of_mem inside, zero_add]

theorem actual_full_forward_action (x : ℝ) : valueRaw observation nontrivial half x =
    burnolInnerGapForward (sourceRaw observation nontrivial half) x +
      burnolInnerGapForward (outsideSourceRaw observation nontrivial half) x + contact observation nontrivial half := by
  have split : burnolInnerGapForward (fullSourceRaw observation nontrivial half) x =
      burnolInnerGapForward (sourceRaw observation nontrivial half) x +
        burnolInnerGapForward (outsideSourceRaw observation nontrivial half) x := by
    rw [forward_cut _ (full_gap observation nontrivial half), forward_cut _ (compact_gap observation nontrivial half),
      forward_cut _ (outside_gap observation nontrivial half), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [actual_full_source_split, mul_add]
  linear_combination split - actual_full_inverse_action observation nontrivial half x

theorem actual_wave_raw : (paWave observation nontrivial half : ℝ → ℂ) =ᵐ[volume]
    fun x => burnolInnerGapForward (sourceRaw observation nontrivial half) x - sourceMean observation nontrivial half := by
  have even : reflectL2 (inverseSource observation nontrivial half) = inverseSource observation nontrivial half := by
    rw [actual_inverse_source]
    exact burnolMobiusSourceL2_even _
  have gap : (inverseSource observation nontrivial half : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval q)] fun _ => 0 := by
    rw [actual_inverse_source]
    exact burnolMobiusSourceL2_innerGap _
  have realizes : ∀ test : SchwartzMap ℝ ℂ,
      burnolRemainderSourceRead (inverseSource observation nontrivial half) test =
        ∫ x : ℝ, test x * paWave observation nontrivial half x := by
    intro test
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      actual_source_action observation nontrivial half test
  obtain ⟨raw, represents, _, wave⟩ := burnolRemainderSourceRead_realization_ae _ _ even gap realizes
  have actual : raw =ᵐ[volume] sourceRaw observation nontrivial half :=
    represents.symm.trans (actual_source_raw observation nontrivial half)
  have mean : (∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) = sourceMean observation nontrivial half :=
    integral_congr_ae ((ae_restrict_of_ae actual).mono
      (fun x same => congrArg (fun z : ℂ => (x : ℂ)⁻¹ * z) same))
  filter_upwards [wave, burnolInnerGapForward_ae_congr _ _ actual] with x value forward
  rw [value, forward, mean]

private theorem response_read :
    (((value observation nontrivial half : BurnolL2) - paWave observation nontrivial half : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      responseRaw observation nontrivial half := by
  filter_upwards [Lp.coeFn_sub (value observation nontrivial half : BurnolL2) (paWave observation nontrivial half),
    actual_value_raw observation nontrivial half, actual_wave_raw observation nontrivial half] with x difference actual wave
  rw [difference]
  change (value observation nontrivial half : BurnolL2) x - paWave observation nontrivial half x = _
  rw [actual, wave, actual_full_forward_action]
  unfold responseRaw
  ring

private theorem response_native : MemLp (responseRaw observation nontrivial half) 2 volume :=
  (Lp.memLp ((value observation nontrivial half : BurnolL2) - paWave observation nontrivial half)).ae_eq
    (response_read observation nontrivial half)

/-- This next response is produced from the independent complete outside inverse and both actual means. -/
def response : BurnolL2 := (response_native observation nontrivial half).toLp (responseRaw observation nontrivial half)

theorem actual_response_raw : (response observation nontrivial half : ℝ → ℂ) =ᵐ[volume]
    responseRaw observation nontrivial half := (response_native observation nontrivial half).coeFn_toLp

theorem actual_source_update : (value observation nontrivial half : BurnolL2) =
    paWave observation nontrivial half + response observation nontrivial half := by
  have read : (value observation nontrivial half : BurnolL2) - paWave observation nontrivial half = response observation nontrivial half :=
    Lp.ext ((response_read observation nontrivial half).trans (actual_response_raw observation nontrivial half).symm)
  exact (sub_eq_iff_eq_add.mp read).trans (add_comm _ _)

end OriginalWholeDebtRJointMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
