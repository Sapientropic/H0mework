import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusAnnulusSource
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Window

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace FourierTransform BigOperators ContDiff
open private source_face_read return_raw_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
open private fourier_c1 row_weight_c1 row_bounds inverse_bounds row_slope_continuous row_derivative from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusAnnulusSource
local notation "q" => (1 / 4 : ℝ)
local notation "h" => J.junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection

theorem actual_source_action (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (inverseSource c) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (paWave c)) test := by
  have row (n : ℕ+) (slot : n ∈ burnolCenteredMobiusCutoffFinset 4) (branch : Fin 2) :
      burnolRemainderSourceRead (rowSource c n branch) test =
        (Lp.toTemperedDistributionCLM ℂ volume 2 (rowWave c n branch)) test := by
    unfold rowSource rowWave
    split_ifs with ordered
    · have bounds := row_bounds n slot branch
      exact burnolWeightedReciprocalStepSource_realizes _ _ _ _
        (inv_pos.mpr (bounds.2.2.trans ordered))
        ((inv_le_inv₀ (bounds.2.2.trans ordered) bounds.2.2).mpr ordered.le)
        (inverse_bounds _ _ bounds.2.2 ordered bounds.1 bounds.2.1).2.2
        (row_slope_continuous c n branch bounds.2.2 ordered).continuousOn test
    · rw [← burnolRemainderSourceReadCLM_apply, map_zero, map_zero]
      rfl
  rw [← burnolRemainderSourceReadCLM_apply test (inverseSource c)]
  simp_rw [inverseSource, paWave, map_sum, map_smul, map_add]
  simp_rw [sum_apply, smul_apply, add_apply, burnolRemainderSourceReadCLM_apply]
  apply Finset.sum_congr rfl
  intro n slot
  rw [row n slot 0, row n slot 1]

/-- Actual row construction, not a source defined from a target residual. -/

def rowRaw (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2) (x : ℝ) : ℂ :=
  if lower n branch < upper n branch then rowWeight c n branch (|x|⁻¹) *
    burnolReciprocalStepSourceRaw (upper n branch)⁻¹ (lower n branch)⁻¹ x else 0

def generatedSourceRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
    Flux.coefficient n * (rowRaw c n 0 x + rowRaw c n 1 x)

private theorem outer_measurable (c : BurnolCompletedMellinCoordinate) (branch : Fin 2) :
    Measurable (jointOuter c branch) := by
  have power : Measurable (fun x : ℝ => (x : ℂ) ^ (-star c.value)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    have nonzero : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
    exact (Complex.continuousAt_ofReal_cpow_const x (-star c.value) (Or.inr nonzero)).continuousWithinAt
  have outer : Measurable (kernelOuter c) :=
    (measurable_const.mul power).sub
      ((burnolRieszReturnRaw_continuous c).measurable.add measurable_const)
  unfold jointOuter
  split_ifs
  · exact ((measurable_const.mul outer).sub
      (((measurable_const.mul (outer.comp (by fun_prop))).add measurable_const).div_const _)).add
        (fourier_c1 (J.sourceSecond c : Hq)).continuous.measurable
  · exact ((measurable_const.mul outer).sub
      (((measurable_const.mul (outer.comp (by fun_prop))).add
        (measurable_const.mul (outer.comp (by fun_prop)))).div_const _)).add
          (fourier_c1 (J.sourceSecond c : Hq)).continuous.measurable

private theorem row_weight_measurable (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2) :
    Measurable (rowWeight c n branch) := by
  unfold rowWeight
  exact (by fun_prop : Measurable (fun x : ℝ => (x : ℂ)⁻¹)).mul
    (((outer_measurable c branch).comp (by fun_prop)).sub measurable_const)

private theorem row_raw_read (c : BurnolCompletedMellinCoordinate) (n : ℕ+)
    (slot : n ∈ burnolCenteredMobiusCutoffFinset 4) (branch : Fin 2) :
    (rowSource c n branch : ℝ → ℂ) =ᵐ[volume] rowRaw c n branch := by
  unfold rowSource rowRaw
  by_cases ordered : lower n branch < upper n branch
  · rw [if_pos ordered]
    simp_rw [if_pos ordered]
    have bounds := row_bounds n slot branch
    have upPositive := bounds.2.2.trans ordered
    have invOrder := (inv_le_inv₀ upPositive bounds.2.2).mpr ordered.le
    have regular : ContinuousOn (rowWeight c n branch)
        (Icc (upper n branch)⁻¹ (lower n branch)⁻¹) :=
      (row_weight_c1 c n branch).continuousOn.mono
        (fun _ inside => (inv_pos.mpr upPositive).trans_le inside.1)
    obtain ⟨bound, bounded⟩ := (isCompact_Icc : IsCompact
      (Icc (upper n branch)⁻¹ (lower n branch)⁻¹)).exists_bound_of_continuousOn regular
    let raw := fun x : ℝ => rowWeight c n branch (|x|⁻¹) *
      burnolReciprocalStepSourceRaw (upper n branch)⁻¹ (lower n branch)⁻¹ x
    have rawNative : MemLp raw 2 volume := by
      apply (burnolReciprocalStepSource_memLp _ _ (inv_pos.mpr upPositive) invOrder).of_le_mul
        (c := bound)
        ((((row_weight_measurable c n branch).comp (by fun_prop)).mul
          (burnolReciprocalStepSource_measurable _ _)).aestronglyMeasurable)
      filter_upwards with x
      change ‖rowWeight c n branch (|x|⁻¹) * burnolReciprocalStepSourceRaw _ _ x‖ ≤ _
      rw [norm_mul]
      by_cases active : (upper n branch)⁻¹ ≤ |x|⁻¹ ∧ |x|⁻¹ < (lower n branch)⁻¹
      · exact mul_le_mul_of_nonneg_right (bounded _ ⟨active.1, active.2.le⟩) (norm_nonneg _)
      · simp only [burnolReciprocalStepSourceRaw, if_neg active, norm_zero, mul_zero, le_refl]
    have same : burnolWeightedReciprocalStepSource (upper n branch)⁻¹ (lower n branch)⁻¹
        (rowWeight c n branch) (rowSlope c n branch) =
        rawNative.toLp raw := by
      apply ext_inner_left ℂ
      intro test
      rw [burnolWeightedReciprocalStepSource_pairing _ _ _ _ (inv_pos.mpr upPositive) invOrder
        (row_derivative c n branch bounds.2.2 ordered)
        (row_slope_continuous c n branch bounds.2.2 ordered).continuousOn
        (row_slope_continuous c n branch bounds.2.2 ordered).measurable, L2.inner_def]
      exact integral_congr_ae (rawNative.coeFn_toLp.symm.mono
        (fun x hx => congrArg (inner ℂ (test x)) hx))
    rw [same]
    exact rawNative.coeFn_toLp
  · rw [if_neg ordered]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x zero
    simpa only [if_neg ordered, Pi.zero_apply] using zero

theorem actual_generated_source_raw (c : BurnolCompletedMellinCoordinate) :
    (inverseSource c : ℝ → ℂ) =ᵐ[volume] generatedSourceRaw c := by
  have rows : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ+ // n ∈ burnolCenteredMobiusCutoffFinset 4},
      (Flux.coefficient n.1 • (rowSource c n.1 0 + rowSource c n.1 1) : BurnolL2) x =
        Flux.coefficient n.1 * (rowRaw c n.1 0 x + rowRaw c n.1 1 x) := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_smul (Flux.coefficient n.1) (rowSource c n.1 0 + rowSource c n.1 1),
      Lp.coeFn_add (rowSource c n.1 0) (rowSource c n.1 1),
      row_raw_read c n.1 n.2 0, row_raw_read c n.1 n.2 1] with x scalar addition first second
    rw [scalar]
    change Flux.coefficient n.1 * (rowSource c n.1 0 + rowSource c n.1 1 : BurnolL2) x = _
    rw [addition]
    change Flux.coefficient n.1 * (rowSource c n.1 0 x + rowSource c n.1 1 x) = _
    rw [first, second]
  filter_upwards [Lp.coeFn_fun_finsetSum (burnolCenteredMobiusCutoffFinset 4)
    (fun n => Flux.coefficient n • (rowSource c n 0 + rowSource c n 1)), rows] with x sum source
  rw [show inverseSource c x = _ from sum]
  exact Finset.sum_congr rfl (fun n slot => source ⟨n, slot⟩)

private theorem kernel_raw_absolute (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszStateRaw c x = if |x| ≤ q then OriginalRieszFinitePairing.positionMean c
      else kernelOuter c |x| := by
  have reflected : burnolRieszStateRaw c x = burnolRieszStateRaw c |x| := by
    rcases le_total 0 x with pos | neg
    · rw [abs_of_nonneg pos]
    · rw [abs_of_nonpos neg, burnolRieszStateRaw_even]
  rw [reflected]
  split_ifs with small
  · exact burnolRieszStateRaw_eq_quarterInner_of_mem c ⟨by linarith [abs_nonneg x], small⟩
  · exact (burnolRieszStateRaw_eq_positiveOuter c (lt_of_not_ge small)).trans
      (OriginalRieszFinitePairing.position_exterior_return_read c |x|)

private theorem correction_fourier_absolute (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    Constructor.fourierRaw (J.sourceSecond c : Hq) x =
      Constructor.fourierRaw (J.sourceSecond c : Hq) |x| := by
  rcases le_total 0 x with pos | neg
  · rw [abs_of_nonneg pos]
  · rw [abs_of_nonpos neg]
    have even := return_raw_even c 0 x
    change Constructor.fourierRaw (J.sourceSecond c : Hq) (-x) - _ =
      Constructor.fourierRaw (J.sourceSecond c : Hq) x - _ at even
    linear_combination -even

private theorem outside_source_raw (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (outside : q < |x|) :
    character c * burnolRieszStateRaw c x - OriginalKPairedBEulerJunctionSource.pairedRaw c 0 x +
      Constructor.fourierRaw (J.sourceSecond c : Hq) x = jointRaw c x := by
  have shift : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr
    OriginalKPairedBEulerJunctionSource.junctionShift_pos.le
  have plusOutside : q < |Real.exp h * x| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos h)]
    nlinarith [abs_nonneg x]
  have inverse : Real.exp h * Real.exp (-h) = 1 := by rw [← Real.exp_add]; simp
  have kernelPlus := kernel_raw_absolute c (Real.exp h * x)
  rw [if_neg (not_le.mpr plusOutside), abs_mul, abs_of_pos (Real.exp_pos h)] at kernelPlus
  rw [jointRaw, if_neg (not_le.mpr outside)]
  rw [kernel_raw_absolute c x, if_neg (not_le.mpr outside), correction_fourier_absolute]
  unfold OriginalKPairedBEulerJunctionSource.pairedRaw OriginalKPairedBEulerJunctionSource.originalRaw
  dsimp only [Matrix.cons_val_zero]
  rw [kernelPlus, kernel_raw_absolute c (Real.exp (-h) * x), abs_mul,
    abs_of_pos (Real.exp_pos (-h))]
  by_cases inside : |x| ≤ q * Real.exp h
  · have inward : Real.exp (-h) * |x| ≤ q := by
      nlinarith [mul_le_mul_of_nonneg_left inside (Real.exp_pos (-h)).le]
    rw [if_pos inward, if_pos inside, jointOuter, if_pos rfl]
  · have outward : q < Real.exp (-h) * |x| := by
      nlinarith [mul_lt_mul_of_pos_left (lt_of_not_ge inside) (Real.exp_pos (-h))]
    rw [if_neg (not_le.mpr outward), if_neg inside, jointOuter, if_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem actual_joint_raw (c : BurnolCompletedMellinCoordinate) :
    (jointValue c : ℝ → ℂ) =ᵐ[volume] jointRaw c := by
  have value : (jointValue c : BurnolL2) = character c • (K c : BurnolL2) - J.sourceAction c +
      OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c := by
    have read := congrArg (fun v : BurnolPaAmbientCarrier => (v : BurnolL2)) (actual_joint_carrier c)
    simp only [Submodule.coe_sub, Submodule.coe_smul] at read
    rw [OriginalKPairedBEulerJunctionSource.BandFullStockEuler.source_action_projection] at read
    exact read.trans (by module)
  have first : (J.sourceAction c : ℝ → ℂ) =ᵐ[volume]
      OriginalKPairedBEulerJunctionSource.pairedRaw c 0 := source_face_read c 0
  have fourier : (fourierL2 (burnolQuarterZeroExtension (J.sourceSecond c : Hq)) : ℝ → ℂ) =ᵐ[volume]
      Constructor.fourierRaw (J.sourceSecond c : Hq) := burnolRadiusFourierL2_zeroExtension_ae_eq_raw _
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolAmbientGap_ae (jointValue c))
  filter_upwards [Lp.coeFn_add (character c • (K c : BurnolL2) - J.sourceAction c)
    (OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c),
    Lp.coeFn_sub (character c • (K c : BurnolL2)) (J.sourceAction c),
    Lp.coeFn_smul (character c) (K c : BurnolL2), burnolRieszState_ae_raw c, first,
    Lp.coeFn_add (burnolQuarterZeroExtension (J.sourceFirst c : Hq))
      (fourierL2 (burnolQuarterZeroExtension (J.sourceSecond c : Hq))),
    burnolQuarterZeroExtension_coe (J.sourceFirst c : Hq), fourier, gap]
      with x addition difference scalar kernel source correction extended transformed inner
  by_cases small : |x| ≤ q
  · rw [jointRaw, if_pos small]
    exact inner (abs_le.mp small)
  · rw [value, addition]
    change (character c • (K c : BurnolL2) - J.sourceAction c : BurnolL2) x +
      OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c x = _
    rw [difference]
    change (character c • (K c : BurnolL2) : BurnolL2) x - J.sourceAction c x + _ = _
    rw [scalar]
    change character c * (K c : BurnolL2) x - J.sourceAction c x + _ = _
    rw [kernel, source]
    change character c * burnolRieszStateRaw c x - OriginalKPairedBEulerJunctionSource.pairedRaw c 0 x +
      (burnolQuarterZeroExtension (J.sourceFirst c : Hq) +
        fourierL2 (burnolQuarterZeroExtension (J.sourceSecond c : Hq)) : BurnolL2) x = _
    rw [correction]
    change character c * burnolRieszStateRaw c x - OriginalKPairedBEulerJunctionSource.pairedRaw c 0 x +
      (burnolQuarterZeroExtension (J.sourceFirst c : Hq) x +
        fourierL2 (burnolQuarterZeroExtension (J.sourceSecond c : Hq)) x) = _
    have outside : x ∉ symmetricInterval q := fun inside => small (abs_le.mpr inside)
    rw [extended, indicator_of_notMem outside, zero_add, transformed]
    exact outside_source_raw c x (lt_of_not_ge small)

private theorem row_interval_read (c : BurnolCompletedMellinCoordinate) (n : ℕ+)
    (slot : n ∈ burnolCenteredMobiusCutoffFinset 4) (branch : Fin 2) (x : ℝ) :
    rowRaw c n branch x = if lower n branch < |x| ∧ |x| ≤ upper n branch then
      jointOuter c branch (|x| / (n : ℕ)) - jointMean c else 0 := by
  have bounds := row_bounds n slot branch
  by_cases ordered : lower n branch < upper n branch
  · have upPositive := bounds.2.2.trans ordered
    rw [rowRaw, if_pos ordered]
    by_cases zero : x = 0
    · subst x
      simp only [abs_zero, inv_zero, burnolReciprocalStepSourceRaw,
        not_le.mpr (inv_pos.mpr upPositive), false_and, if_false, mul_zero,
        not_lt.mpr bounds.2.2.le]
    · have xp := abs_pos.mpr zero
      have incidence : (upper n branch)⁻¹ ≤ |x|⁻¹ ∧ |x|⁻¹ < (lower n branch)⁻¹ ↔
          lower n branch < |x| ∧ |x| ≤ upper n branch := by
        rw [inv_le_inv₀ upPositive xp, inv_lt_inv₀ xp bounds.2.2, and_comm]
      unfold burnolReciprocalStepSourceRaw
      simp only [incidence]
      split_ifs with active
      · unfold rowWeight
        simp only [inv_inv, Complex.ofReal_inv]
        field_simp [Complex.ofReal_ne_zero.mpr xp.ne']
      · exact mul_zero _
  · have inactive : ¬(lower n branch < |x| ∧ |x| ≤ upper n branch) :=
      fun active => ordered (active.1.trans_le active.2)
    rw [rowRaw, if_neg ordered, if_neg inactive]

private theorem row_joint_read (c : BurnolCompletedMellinCoordinate) (n : ℕ+)
    (slot : n ∈ burnolCenteredMobiusCutoffFinset 4) (x : ℝ) :
    rowRaw c n 0 x + rowRaw c n 1 x =
      (symmetricInterval (4 : ℝ)).indicator
        (fun x => jointRaw c (x / (n : ℕ)) - jointMean c) x := by
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have shift : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr
    OriginalKPairedBEulerJunctionSource.junctionShift_pos.le
  have nonnegative : 0 ≤ ((n : ℕ) : ℝ) * q := by positivity
  rw [row_interval_read c n slot 0 x, row_interval_read c n slot 1 x]
  have firstLower : lower n 0 = (n : ℕ) * q := by simp [lower]
  have secondLower : lower n 1 = (n : ℕ) * q * Real.exp h := by simp [lower]
  have firstUpper : upper n 0 = min 4 ((n : ℕ) * q * Real.exp h) := by simp [upper]
  have secondUpper : upper n 1 = 4 := by simp [upper]
  rw [firstLower, secondLower, firstUpper, secondUpper]
  by_cases inside : |x| ≤ (4 : ℝ)
  · have membership : x ∈ symmetricInterval (4 : ℝ) := abs_le.mp inside
    rw [Set.indicator_of_mem membership]
    unfold jointRaw
    rw [abs_div, abs_of_pos np]
    by_cases small : |x| ≤ (n : ℕ) * q
    · have smallDiv : |x| / (n : ℕ) ≤ q := (div_le_iff₀ np).mpr (by nlinarith)
      have smallSecond : |x| ≤ (n : ℕ) * q * Real.exp h := by
        nlinarith [mul_le_mul_of_nonneg_left shift nonnegative]
      rw [if_pos smallDiv, sub_self, if_neg (fun active => not_lt_of_ge small active.1),
        if_neg (fun active => not_lt_of_ge smallSecond active.1), add_zero]
    · have beyond : (n : ℕ) * q < |x| := lt_of_not_ge small
      have beyondDiv : ¬|x| / (n : ℕ) ≤ q := by
        intro low
        have same := (div_le_iff₀ np).mp low
        nlinarith
      rw [if_neg beyondDiv]
      by_cases firstBand : |x| ≤ (n : ℕ) * q * Real.exp h
      · have firstDiv : |x| / (n : ℕ) ≤ q * Real.exp h := (div_le_iff₀ np).mpr (by nlinarith)
        rw [if_pos ⟨beyond, le_min inside firstBand⟩,
          if_neg (fun active => not_lt_of_ge firstBand active.1), add_zero, if_pos firstDiv]
      · have secondDiv : ¬|x| / (n : ℕ) ≤ q * Real.exp h := by
          intro low
          have same := (div_le_iff₀ np).mp low
          apply firstBand
          nlinarith
        have notFirst : ¬((n : ℕ) * q < |x| ∧ |x| ≤ min 4 ((n : ℕ) * q * Real.exp h)) :=
          fun active => firstBand (active.2.trans (min_le_right _ _))
        rw [if_neg notFirst, zero_add, if_pos ⟨lt_of_not_ge firstBand, inside⟩, if_neg secondDiv]
  · have outside : x ∉ symmetricInterval (4 : ℝ) := fun small => inside (abs_le.mpr small)
    rw [indicator_of_notMem outside]
    have noFirst : ¬((n : ℕ) * q < |x| ∧ |x| ≤ min 4 ((n : ℕ) * q * Real.exp h)) :=
      fun active => inside (active.2.trans (min_le_left _ _))
    rw [if_neg noFirst, if_neg (fun active => inside active.2), add_zero]

theorem actual_source_raw (c : BurnolCompletedMellinCoordinate) :
    (inverseSource c : ℝ → ℂ) =ᵐ[volume] sourceRaw c := by
  filter_upwards [actual_generated_source_raw c] with x actual
  rw [actual]
  unfold generatedSourceRaw sourceRaw
  by_cases inside : x ∈ symmetricInterval (4 : ℝ)
  · rw [Set.indicator_of_mem inside]
    apply Finset.sum_congr rfl
    intro n slot
    rw [row_joint_read c n slot x, Set.indicator_of_mem inside]
  · rw [Set.indicator_of_notMem inside]
    apply Finset.sum_eq_zero
    intro n slot
    rw [row_joint_read c n slot x, Set.indicator_of_notMem inside, mul_zero]

theorem actual_joint_inverse_source (c : BurnolCompletedMellinCoordinate) :
    inverseSource c = burnolMobiusSourceL2 (jointValue c) := by
  have scaled (n : ℕ+) : ∀ᵐ x : ℝ ∂volume,
      (jointValue c : BurnolL2) (x / (n : ℕ)) = jointRaw c (x / (n : ℕ)) := by
    have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := ((n : ℕ) : ℝ)⁻¹) (inv_ne_zero np.ne')
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using qmp.ae (actual_joint_raw c)
  have window := (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
    (burnolMobiusWindowSourceRead_coeFn (jointValue c))
  apply Lp.ext
  filter_upwards [actual_source_raw c, burnolRadiusZeroExtension_coe
    (burnolMobiusWindowSourceRead (jointValue c)), window, ae_all_iff.mpr scaled]
      with x source extended read raw
  change inverseSource c x = burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead (jointValue c)) x
  rw [source, extended]
  unfold sourceRaw
  by_cases inside : x ∈ symmetricInterval (4 : ℝ)
  · rw [indicator_of_mem inside, indicator_of_mem inside, read inside]
    apply Finset.sum_congr rfl
    intro n _
    rw [raw n]
    rfl
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

end OriginalWholeDebtRJointMobiusSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
