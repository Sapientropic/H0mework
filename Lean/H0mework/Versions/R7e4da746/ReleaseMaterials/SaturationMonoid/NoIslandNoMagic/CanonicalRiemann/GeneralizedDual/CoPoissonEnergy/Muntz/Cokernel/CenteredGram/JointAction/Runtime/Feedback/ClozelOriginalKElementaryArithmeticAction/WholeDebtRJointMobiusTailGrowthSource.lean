import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusUnitSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusTemperedSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators ArithmeticFunction
namespace J
export OriginalWholeDebtRJointMobiusSource
  (jointRaw jointMean jointValue kernelOuter jointOuter character actual_joint_raw)
end J
namespace U
export OriginalWholeDebtRJointMobiusUnitSource (sourceRaw unitRaw unitCoefficient)
end U
local notation "q" => (1 / 4 : ℝ)
local notation "h" => OriginalKPairedBEulerJunctionSource.junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => volume.restrict (symmetricInterval q)

private def fourierMass (state : Hq) : ℝ := ∫ t : ℝ, ‖state t‖ ∂μq
private theorem fourier_mass_nonneg (state : Hq) : 0 ≤ fourierMass state := integral_nonneg (fun _ => norm_nonneg _)
private theorem fourier_bound (state : Hq) (x : ℝ) :
    ‖Constructor.fourierRaw state x‖ ≤ fourierMass state :=
  VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 μq (innerₗ ℝ) state x

private def lower : ℝ := q * Real.exp (-h)
private theorem lower_pos : 0 < lower := by unfold lower; positivity
private theorem lower_le_quarter : lower ≤ q := by
  unfold lower
  have small : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr OriginalKPairedBEulerJunctionSource.junctionShift_pos.le)
  nlinarith
private def kernelBound (c : BurnolCompletedMellinCoordinate) : ℝ :=
  (1 / 2 : ℝ) * lower ^ (-c.value.re) + fourierMass (burnolRieszSingleFourierSource c : Hq)
private theorem kernel_bound_nonneg (c : BurnolCompletedMellinCoordinate) : 0 ≤ kernelBound c := by
  unfold kernelBound
  exact add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg lower_pos.le _)) (fourier_mass_nonneg _)
private theorem kernel_bound (c : BurnolCompletedMellinCoordinate) {x : ℝ} (large : lower ≤ x) :
    ‖J.kernelOuter c x‖ ≤ kernelBound c := by
  have xp : 0 < x := lower_pos.trans_le large
  have power : ‖(x : ℂ) ^ (-star c.value)‖ ≤ lower ^ (-c.value.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos xp]
    change x ^ (-c.value.re) ≤ lower ^ (-c.value.re)
    exact Real.rpow_le_rpow_of_nonpos lower_pos large (by linarith [c.rightHalf])
  have raw : J.kernelOuter c x = (1 / 2 : ℂ) * (x : ℂ) ^ (-star c.value) -
      Constructor.fourierRaw (burnolRieszSingleFourierSource c : Hq) x := by
    unfold OriginalWholeDebtRJointMobiusSource.kernelOuter burnolRieszReturnRaw burnolMeanZeroFourierRaw
    rw [sub_add_cancel]
    rfl
  rw [raw]
  calc
    _ ≤ ‖(1 / 2 : ℂ) * (x : ℂ) ^ (-star c.value)‖ +
      ‖Constructor.fourierRaw (burnolRieszSingleFourierSource c : Hq) x‖ := norm_sub_le _ _
    _ ≤ kernelBound c := by
      rw [norm_mul]
      norm_num only [norm_div, norm_one, norm_ofNat]
      exact add_le_add (mul_le_mul_of_nonneg_left power (by norm_num)) (fourier_bound _ x)

private def outerBound (c : BurnolCompletedMellinCoordinate) : ℝ :=
  ‖J.character c‖ * kernelBound c +
    (‖(Real.exp (h / 2) : ℂ)‖ * kernelBound c + ‖(Real.exp (-h / 2) : ℂ)‖ *
      (‖OriginalRieszFinitePairing.positionMean c‖ + kernelBound c)) / 2 +
    fourierMass (OriginalKPairedBEulerJunctionSource.sourceSecond c : Hq)
private theorem outer_bound_nonneg (c : BurnolCompletedMellinCoordinate) : 0 ≤ outerBound c := by
  have kernel := kernel_bound_nonneg c
  have mass := fourier_mass_nonneg (OriginalKPairedBEulerJunctionSource.sourceSecond c : Hq)
  unfold outerBound
  positivity
private theorem outer_bound (c : BurnolCompletedMellinCoordinate) (branch : Fin 2)
    {x : ℝ} (large : q ≤ x) : ‖J.jointOuter c branch x‖ ≤ outerBound c := by
  have base := kernel_bound c (lower_le_quarter.trans large)
  have ep : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr OriginalKPairedBEulerJunctionSource.junctionShift_pos.le
  have plus := kernel_bound c (show lower ≤ Real.exp h * x by nlinarith [lower_le_quarter])
  have minus := kernel_bound c (show lower ≤ Real.exp (-h) * x by
    unfold lower
    simpa only [mul_comm q] using mul_le_mul_of_nonneg_left large (Real.exp_pos (-h)).le)
  have branchBound : ‖(if branch = 0 then OriginalRieszFinitePairing.positionMean c
      else J.kernelOuter c (Real.exp (-h) * x))‖ ≤
      ‖OriginalRieszFinitePairing.positionMean c‖ + kernelBound c := by
    split_ifs
    · exact le_add_of_nonneg_right (kernel_bound_nonneg c)
    · exact minus.trans (le_add_of_nonneg_left (norm_nonneg _))
  unfold OriginalWholeDebtRJointMobiusSource.jointOuter
  calc
    _ ≤ ‖J.character c * J.kernelOuter c x -
        ((Real.exp (h / 2) : ℂ) * J.kernelOuter c (Real.exp h * x) +
          (Real.exp (-h / 2) : ℂ) * (if branch = 0 then OriginalRieszFinitePairing.positionMean c
            else J.kernelOuter c (Real.exp (-h) * x))) / 2‖ +
        ‖Constructor.fourierRaw (OriginalKPairedBEulerJunctionSource.sourceSecond c : Hq) x‖ := norm_add_le _ _
    _ ≤ (‖J.character c * J.kernelOuter c x‖ +
        ‖((Real.exp (h / 2) : ℂ) * J.kernelOuter c (Real.exp h * x) +
          (Real.exp (-h / 2) : ℂ) * (if branch = 0 then OriginalRieszFinitePairing.positionMean c
            else J.kernelOuter c (Real.exp (-h) * x))) / 2‖) +
        fourierMass (OriginalKPairedBEulerJunctionSource.sourceSecond c : Hq) :=
      add_le_add (norm_sub_le _ _) (fourier_bound _ x)
    _ ≤ outerBound c := by
      rw [norm_mul, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have triangle := norm_add_le
        ((Real.exp (h / 2) : ℂ) * J.kernelOuter c (Real.exp h * x))
        ((Real.exp (-h / 2) : ℂ) * (if branch = 0 then OriginalRieszFinitePairing.positionMean c
          else J.kernelOuter c (Real.exp (-h) * x)))
      simp only [norm_mul] at triangle
      unfold outerBound
      gcongr
      exact triangle.trans (add_le_add
        (mul_le_mul_of_nonneg_left plus (norm_nonneg _))
        (mul_le_mul_of_nonneg_left branchBound (norm_nonneg _)))

/-- Both actual original B/Fourier profiles give a coarse global bound; no arithmetic tail estimate is used. -/
theorem actual_joint_uniform_bound (c : BurnolCompletedMellinCoordinate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖J.jointRaw c x‖ ≤ C := by
  refine ⟨‖J.jointMean c‖ + outerBound c, add_nonneg (norm_nonneg _) (outer_bound_nonneg c), ?_⟩
  intro x
  unfold OriginalWholeDebtRJointMobiusSource.jointRaw
  split_ifs with small middle
  · exact le_add_of_nonneg_right (outer_bound_nonneg c)
  · exact (outer_bound c 0 (le_of_not_ge small)).trans (le_add_of_nonneg_left (norm_nonneg _))
  · exact (outer_bound c 1 (le_of_not_ge small)).trans (le_add_of_nonneg_left (norm_nonneg _))

private theorem joint_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ} (small : |x| ≤ q) :
    J.jointRaw c x = J.jointRaw c 0 := by
  simp only [OriginalWholeDebtRJointMobiusSource.jointRaw, if_pos small, abs_zero,
    show (0 : ℝ) ≤ q by norm_num, ↓reduceIte]

private theorem inverse_bound (raw : ℝ → ℂ)
    (gap : ∀ {x : ℝ}, |x| ≤ q → raw x = raw 0)
    (C : ℝ) (nonnegative : 0 ≤ C) (bound : ∀ x, ‖raw x‖ ≤ C) (x : ℝ) :
    ‖burnolCenteredMobiusInverse raw x‖ ≤ (2 * C) * (4 * |x| + 1) := by
  classical
  rw [burnolCenteredMobiusInverse_eq_cutoffSum raw gap]
  have summand (n : ℕ+) : ‖burnolCenteredMobiusSummand raw x n‖ ≤ 2 * C := by
    have mu : ‖(ArithmeticFunction.moebius (n : ℕ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := (n : ℕ)))
    have denominator : ‖(((n : ℕ) : ℂ)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast n.pos)
    unfold burnolCenteredMobiusSummand
    rw [norm_mul, norm_mul]
    calc
      _ ≤ 1 * (1 * (‖raw (x / (n : ℕ))‖ + ‖raw 0‖)) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ 2 * C := by nlinarith [bound (x / (n : ℕ)), bound 0]
  have card : (burnolCenteredMobiusCutoffFinset x).card ≤ burnolCenteredMobiusCutoff x := by
    simpa only [Finset.card_range] using Finset.card_le_card_of_injOn
      (s := burnolCenteredMobiusCutoffFinset x) (t := Finset.range (burnolCenteredMobiusCutoff x))
      (fun n : ℕ+ => (n : ℕ))
      (fun n member => Finset.mem_range.mpr ((mem_burnolCenteredMobiusCutoffFinset x n).mp member))
      (Set.injOn_of_injective PNat.coe_injective)
  calc
    _ ≤ ∑ n ∈ burnolCenteredMobiusCutoffFinset x, ‖burnolCenteredMobiusSummand raw x n‖ := norm_sum_le _ _
    _ ≤ (burnolCenteredMobiusCutoffFinset x).card * (2 * C) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun n (_ : n ∈ burnolCenteredMobiusCutoffFinset x) => summand n)
    _ ≤ (2 * C) * (4 * |x| + 1) := by
      have natural : ((burnolCenteredMobiusCutoffFinset x).card : ℝ) ≤ (burnolCenteredMobiusCutoff x : ℝ) := by exact_mod_cast card
      have count : ((burnolCenteredMobiusCutoffFinset x).card : ℝ) ≤ 4 * |x| + 1 :=
        natural.trans (by
          unfold burnolCenteredMobiusCutoff
          exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * |x|)).le)
      nlinarith

/-- The complete independent inverse tail has polynomial growth; this qualifies it without changing its raw carrier. -/
theorem actual_source_growth (c : BurnolCompletedMellinCoordinate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖U.sourceRaw c x‖ ≤ C * (1 + |x|) := by
  obtain ⟨B, positive, bound⟩ := actual_joint_uniform_bound c
  have inverse := inverse_bound (J.jointRaw c) (joint_gap c) B positive bound
  have unitBound (x : ℝ) : ‖U.unitRaw c x‖ ≤ 1 := by
    unfold OriginalWholeDebtRJointMobiusUnitSource.unitRaw burnolRadiusUnitTailRaw
    split_ifs with outside
    · rw [norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [abs_nonneg x] : 0 < |x|)]
      simp only [neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [c.rightHalf])
    · simp only [norm_zero, zero_le_one]
  refine ⟨8 * B + ‖U.unitCoefficient c‖, by positivity, ?_⟩
  intro x
  have outside : ‖OriginalWholeDebtRJointMobiusProgramme.outsideSourceRaw c x‖ ≤
      (2 * B) * (4 * |x| + 1) := by
    unfold OriginalWholeDebtRJointMobiusProgramme.outsideSourceRaw
    by_cases inside : x ∈ (symmetricInterval (4 : ℝ))ᶜ
    · rw [indicator_of_mem inside]
      exact inverse x
    · rw [indicator_of_notMem inside, norm_zero]
      positivity
  unfold OriginalWholeDebtRJointMobiusUnitSource.sourceRaw
  calc
    _ ≤ ‖OriginalWholeDebtRJointMobiusProgramme.outsideSourceRaw c x‖ +
        ‖U.unitCoefficient c * U.unitRaw c x‖ := norm_sub_le _ _
    _ ≤ (8 * B + ‖U.unitCoefficient c‖) * (1 + |x|) := by
      rw [norm_mul]
      have scaled := mul_le_mul_of_nonneg_left (unitBound x) (norm_nonneg (U.unitCoefficient c))
      have remaining : 0 ≤ ‖U.unitCoefficient c‖ * |x| := mul_nonneg (norm_nonneg _) (abs_nonneg _ )
      nlinarith


private theorem source_measurable (c : BurnolCompletedMellinCoordinate) :
    AEStronglyMeasurable (U.sourceRaw c) volume := by
  have joint : AEStronglyMeasurable (J.jointRaw c) volume :=
    (Lp.aestronglyMeasurable (J.jointValue c : BurnolL2)).congr (J.actual_joint_raw c)
  have full : AEMeasurable (OriginalWholeDebtRJointMobiusProgramme.fullSourceRaw c) volume := by
    unfold OriginalWholeDebtRJointMobiusProgramme.fullSourceRaw burnolCenteredMobiusInverse
    apply AEMeasurable.tsum
    intro n
    have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x / (n : ℕ)) volume volume := by
      simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using
        Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
          (r := ((n : ℕ) : ℝ)⁻¹) (inv_ne_zero (by exact_mod_cast n.ne_zero))
    exact (((joint.comp_quasiMeasurePreserving qmp).sub aestronglyMeasurable_const).const_mul
      (((n : ℕ) : ℂ)⁻¹)).aemeasurable.const_mul (ArithmeticFunction.moebius (n : ℕ) : ℂ)
  have unit : AEStronglyMeasurable (U.unitRaw c) volume :=
    (Lp.aestronglyMeasurable (burnolRadiusNormalizedUnitTail c 4 (by norm_num))).congr
      (burnolRadiusUnitTail_coeFn c 4 (by norm_num))
  exact ((full.indicator (measurableSet_symmetricInterval (4 : ℝ)).compl).aestronglyMeasurable.sub
    (unit.const_mul (U.unitCoefficient c)))

end OriginalWholeDebtRJointMobiusTemperedSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
