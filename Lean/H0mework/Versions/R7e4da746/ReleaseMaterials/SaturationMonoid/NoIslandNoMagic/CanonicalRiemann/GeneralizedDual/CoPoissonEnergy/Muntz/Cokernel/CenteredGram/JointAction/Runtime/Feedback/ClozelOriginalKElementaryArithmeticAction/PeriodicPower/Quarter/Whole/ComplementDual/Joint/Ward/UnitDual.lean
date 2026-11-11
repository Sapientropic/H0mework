import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.SeedClock

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open scoped InnerProductSpace Topology
open private mean_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "D" => burnolMultiplicativeDilation

def seedCut (coordinate : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  (symmetricInterval q).indicator (seedRaw coordinate.value)

def halfPower (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * powerRaw coordinate.value x

def homogeneousPrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  ∫ x : ℝ, star (value x) * halfPower coordinate x

/-- The same seed pays the entire original quarter mean before any projection or Mellin read. -/
theorem actual_gap_seed_raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x + seedCut coordinate x =
      halfPower coordinate x := by
  by_cases inside : x ∈ symmetricInterval q
  · rw [seedCut, indicator_of_mem inside, gapState_raw_gap coordinate inside, seedRaw]
    unfold halfPower
    linear_combination -(mean_power coordinate)
  · rw [seedCut, indicator_of_notMem inside, add_zero]
    have outside : q < |x| := by
      by_contra no
      exact inside (abs_le.mp (le_of_not_gt no))
    by_cases positive : 0 ≤ x
    · have after : q < x := by simpa only [abs_of_nonneg positive] using outside
      rw [gapState_raw_tail coordinate after]
      simp only [halfPower, powerRaw, abs_of_nonneg positive]
    · have after : q < -x := by simpa only [abs_of_neg (lt_of_not_ge positive)] using outside
      have even : burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x =
          burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) (-x) := by
        simp only [burnolEvenRaw, neg_neg]
        ring
      rw [even, gapState_raw_tail coordinate after]
      simp only [halfPower, powerRaw, abs_of_neg (lt_of_not_ge positive)]

private theorem halfPower_dilation (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    halfPower coordinate (Real.exp h * x) =
      Complex.exp (-star coordinate.value * (h : ℂ)) * halfPower coordinate x := by
  unfold halfPower powerRaw
  rw [abs_mul, abs_of_pos (Real.exp_pos h), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h).le (abs_nonneg x),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)),
    ← Complex.ofReal_log (Real.exp_pos h).le, Real.log_exp]
  ring

private theorem homogeneous_dilation_product (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (value : BurnolL2) :
    (fun x : ℝ => star (D h value x) * halfPower coordinate x) =ᵐ[volume]
      fun x : ℝ => Complex.exp ((star coordinate.value + 1 / 2) * (h : ℂ)) *
        (star (value (Real.exp h * x)) * halfPower coordinate (Real.exp h * x)) := by
  have phase : Complex.exp ((star coordinate.value + 1 / 2) * (h : ℂ)) *
      Complex.exp (-star coordinate.value * (h : ℂ)) = (Real.exp (h / 2) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  filter_upwards [burnolMultiplicativeDilation_coeFn h value] with x source
  rw [source]
  change star ((Real.exp (h / 2) : ℂ) * value (Real.exp h * x)) * halfPower coordinate x = _
  rw [star_mul, show star (Real.exp (h / 2) : ℂ) = (Real.exp (h / 2) : ℂ) from Complex.conj_ofReal _,
    halfPower_dilation]
  linear_combination -star (value (Real.exp h * x)) * halfPower coordinate x * phase

theorem actual_homogeneous_price_dilation (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (value : BurnolL2) :
    homogeneousPrice coordinate (D h value) =
      fullMellinTranslationCharacter (star coordinate.value) (-h) * homogeneousPrice coordinate value := by
  rw [homogeneousPrice, integral_congr_ae (homogeneous_dilation_product coordinate h value), integral_const_mul]
  change Complex.exp ((star coordinate.value + 1 / 2) * (h : ℂ)) *
    (∫ x : ℝ, (fun y : ℝ => star (value y) * halfPower coordinate y) (Real.exp h * x)) = _
  rw [Measure.integral_comp_mul_left (fun y : ℝ => star (value y) * halfPower coordinate y) (Real.exp h),
    abs_of_pos (inv_pos.mpr (Real.exp_pos h)), Complex.real_smul, Complex.ofReal_inv]
  unfold homogeneousPrice fullMellinTranslationCharacter
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_neg, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem homogeneous_dilation_domain (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (value : BurnolL2)
    (domain : Integrable (fun x : ℝ => star (value x) * halfPower coordinate x)) :
    Integrable (fun x : ℝ => star (D h value x) * halfPower coordinate x) := by
  exact ((domain.comp_mul_left' (Real.exp_ne_zero h)).const_mul
    (Complex.exp ((star coordinate.value + 1 / 2) * (h : ℂ)))).congr
      (homogeneous_dilation_product coordinate h value).symm

private theorem seed_indicator_product (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (fun x : ℝ => star (value x) * seedCut coordinate x) =
      (symmetricInterval q).indicator (fun x : ℝ => star (value x) * seedRaw coordinate.value x) := by
  funext x
  by_cases inside : x ∈ symmetricInterval q
  · simp only [seedCut, indicator_of_mem inside]
  · simp only [seedCut, indicator_of_notMem inside, mul_zero]

private theorem physical_seed_price (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier) :
    Integrable (fun x : ℝ => star ((value : BurnolL2) x) * seedCut coordinate x) ∧
      (∫ x : ℝ, star ((value : BurnolL2) x) * seedCut coordinate x) = 0 := by
  obtain ⟨coefficient, gap⟩ := mem_locallyConstantFace_iff_exists.mp value.property.1.1
  change coefficient • intervalConstant q = Rq (value : BurnolL2) at gap
  have same : ((value : BurnolL2) : ℝ → ℂ) =ᵐ[μq] fun _ => coefficient := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (value : BurnolL2),
      Lp.coeFn_smul coefficient (intervalConstant q), intervalConstant_coeFn q] with x restricted scalar constant
    have read := congrArg (fun state : Hq => state x) gap
    change Rq (value : BurnolL2) x = (value : BurnolL2) x at restricted
    rw [scalar, Pi.smul_apply, smul_eq_mul, constant, mul_one, restricted] at read
    exact read.symm
  have domain : Integrable (fun x : ℝ => star ((value : BurnolL2) x) * seedRaw coordinate.value x) μq :=
    ((actual_seed_integrable coordinate.value coordinate.belowOne).const_mul (star coefficient)).congr
      (same.mono (fun x read => by dsimp only at read ⊢; rw [read]))
  rw [seed_indicator_product]
  refine ⟨(integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr domain, ?_⟩
  rw [integral_indicator (measurableSet_symmetricInterval q)]
  calc
    _ = star coefficient * ∫ x : ℝ, seedRaw coordinate.value x ∂μq := by
      rw [← integral_const_mul]
      exact integral_congr_ae (same.mono (fun x read => by dsimp only at read ⊢; rw [read]))
    _ = 0 := by rw [actual_seed_mean coordinate.value coordinate.belowOne, mul_zero]

private theorem physical_homogeneous_price (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier) :
    Integrable (fun x : ℝ => star ((value : BurnolL2) x) * halfPower coordinate x) ∧
      homogeneousPrice coordinate (value : BurnolL2) = inner ℂ (value : BurnolL2) (gapState coordinate) := by
  have gapDomain : Integrable (fun x : ℝ => star ((value : BurnolL2) x) * gapState coordinate x) :=
    by simpa only [RCLike.inner_apply', starRingEnd_apply] using
      L2.integrable_inner (𝕜 := ℂ) (value : BurnolL2) (gapState coordinate)
  have source : (fun x : ℝ => star ((value : BurnolL2) x) * halfPower coordinate x) =ᵐ[volume]
      fun x : ℝ => star ((value : BurnolL2) x) * gapState coordinate x +
        star ((value : BurnolL2) x) * seedCut coordinate x := by
    filter_upwards [gapState_read coordinate] with x source
    rw [source, ← mul_add, actual_gap_seed_raw]
  have seed := physical_seed_price coordinate value
  refine ⟨(gapDomain.add seed.1).congr source.symm, ?_⟩
  rw [homogeneousPrice, integral_congr_ae source, integral_add gapDomain seed.1, seed.2, add_zero]
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', starRingEnd_apply]

private theorem actual_dual_pair_price (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (domain : Integrable (fun x : ℝ => star (value x) * halfPower coordinate x)) :
    (∫ x : ℝ, star (value x) * dualRaw coordinate.value coordinate.belowOne x ∂μq) =
      inner ℂ (Rq value)
        (S (smooth (dualRaw coordinate.value coordinate.belowOne)
          (actual_dual_integrable coordinate.value coordinate.belowOne)) : Hq) +
      homogeneousPrice coordinate value - inner ℂ value (gapState coordinate) := by
  let corr := correction coordinate.value coordinate.belowOne
  have actualCorr : S (smooth (dualRaw coordinate.value coordinate.belowOne)
      (actual_dual_integrable coordinate.value coordinate.belowOne)) = corr := by
    rw [actual_original_dual_fourier_source, map_sub, map_smul]
    exact (actual_original_dual_correction coordinate).symm
  have gapDomain : Integrable (fun x : ℝ => star (value x) * gapState coordinate x) :=
    by simpa only [RCLike.inner_apply', starRingEnd_apply] using
      L2.integrable_inner (𝕜 := ℂ) value (gapState coordinate)
  have source : (fun x : ℝ => star (value x) * seedCut coordinate x) =ᵐ[volume]
      fun x : ℝ => star (value x) * halfPower coordinate x - star (value x) * gapState coordinate x := by
    filter_upwards [gapState_read coordinate] with x source
    rw [source]
    linear_combination star (value x) * actual_gap_seed_raw coordinate x
  have seedDomain := (domain.sub gapDomain).congr source.symm
  have seedQuarter : Integrable (fun x : ℝ => star (value x) * seedRaw coordinate.value x) μq := by
    rw [seed_indicator_product] at seedDomain
    exact (integrable_indicator_iff (measurableSet_symmetricInterval q)).mp seedDomain
  have seedPrice : (∫ x : ℝ, star (value x) * seedRaw coordinate.value x ∂μq) =
      homogeneousPrice coordinate value - inner ℂ value (gapState coordinate) := by
    rw [← integral_indicator (measurableSet_symmetricInterval q), ← seed_indicator_product,
      integral_congr_ae source, integral_sub domain gapDomain]
    rw [L2.inner_def]
    simp only [homogeneousPrice, RCLike.inner_apply', starRingEnd_apply]
  have corrSource : (fun x : ℝ => star (value x) * correctionRaw coordinate.value coordinate.belowOne x) =ᵐ[μq]
      fun x : ℝ => star (Rq value x) * (corr : Hq) x := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
      actual_correction_raw coordinate.value coordinate.belowOne] with x restricted raw
    change Rq value x = value x at restricted
    change (corr : Hq) x = correctionRaw coordinate.value coordinate.belowOne x at raw
    rw [restricted, raw]
  have corrDomain : Integrable (fun x : ℝ => star (value x) * correctionRaw coordinate.value coordinate.belowOne x) μq :=
    (show Integrable (fun x : ℝ => star (Rq value x) * (corr : Hq) x) μq from
      by simpa only [RCLike.inner_apply', starRingEnd_apply] using
        L2.integrable_inner (𝕜 := ℂ) (Rq value) (corr : Hq)).congr corrSource.symm
  have corrPrice : (∫ x : ℝ, star (value x) * correctionRaw coordinate.value coordinate.belowOne x ∂μq) =
      inner ℂ (Rq value) (corr : Hq) := by
    rw [L2.inner_def]
    simpa only [RCLike.inner_apply', starRingEnd_apply] using integral_congr_ae corrSource
  simp only [dualRaw, mul_add]
  rw [integral_add seedQuarter corrDomain, seedPrice, corrPrice, actualCorr]
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

theorem actual_native_unit_positive_dual_top (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (U (m - 1)) (D h (nativeReturn c)) =
      (∫ x : ℝ, star (D h (fourierL2 (U (m - 1))) x) * dualRaw (c).value (c).belowOne x ∂μq) -
        fullMellinTranslationCharacter (star (c).value) (-h) * star e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  let unit : BurnolPaAmbientCarrier :=
    ⟨U (m - 1), OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half
      (m - 1) (by omega)⟩
  let physical := evenFaceFourierEquiv q unit
  have paid := physical_homogeneous_price c physical
  have gapPrice : inner ℂ (gapState c) (physical : BurnolL2) = e := by
    rw [gapState_eq_kernel_add_correction, inner_add_left, sourceCorrection_eq_generated,
      burnolAmbientEvenMeanZeroCorrection_inner_physical_eq_zero, add_zero]
    have moved := fourierL2.inner_map_map
      (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)) (U (m - 1))
    rw [fourierL2_fourierL2, mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2] at moved
    exact moved.trans (OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_top observation nontrivial half)
  have initial : homogeneousPrice c (physical : BurnolL2) = star e := by
    rw [paid.2, ← inner_conj_symm, gapPrice]
    rfl
  have acted : homogeneousPrice c (D h (fourierL2 (U (m - 1)))) =
      fullMellinTranslationCharacter (star (c).value) (-h) * star e := by
    change homogeneousPrice c (D h (physical : BurnolL2)) = _
    rw [actual_homogeneous_price_dilation, initial]
  have pair := actual_dual_pair_price c (D h (fourierL2 (U (m - 1))))
    (homogeneous_dilation_domain c h (physical : BurnolL2) paid.1)
  rw [actual_native_unit_positive_source observation nontrivial half (m - 1) (by omega) h nonnegative,
    pair, acted]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
