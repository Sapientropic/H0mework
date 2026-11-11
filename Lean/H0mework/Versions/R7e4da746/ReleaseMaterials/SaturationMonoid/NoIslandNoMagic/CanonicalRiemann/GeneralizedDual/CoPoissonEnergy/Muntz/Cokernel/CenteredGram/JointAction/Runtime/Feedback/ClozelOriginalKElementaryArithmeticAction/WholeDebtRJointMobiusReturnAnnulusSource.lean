import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTateRSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Joint
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.RemainderClosedRange

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusReturnSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators ContDiff ArithmeticFunction
namespace T
export OriginalWholeDebtRJointMobiusTateRSource
  (updatedWave actionRaw outwardRaw homogeneousCoefficient powerRaw actual_outward_gap)
end T
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

/-- The complete B correction is removed from the already generated whole wave. -/
def value : BurnolPaAmbientCarrier := P w

def second : BurnolQuarterMeanZeroCarrier := burnolAmbientMeanZeroSecondCorrection w

def contact : ℂ := burnolProjectionGapRaw w

def outerProfile (x : ℝ) : ℂ :=
  T.homogeneousCoefficient coord * T.powerRaw coord x -
    (Constructor.fourierRaw (second observation nontrivial half : Hq) x +
      Constructor.fourierRaw (second observation nontrivial half : Hq) (-x)) / 2

def valueRaw : ℝ → ℂ := burnolEvenProjectionRaw w (T.actionRaw coord)

private theorem whole_raw : (w : ℝ → ℂ) =ᵐ[volume] T.actionRaw coord := by
  rw [OriginalWholeDebtRJointMobiusTateRSource.actual_updated_wave]
  exact OriginalWholeDebtRJointMobiusTateRSource.actual_whole_action observation nontrivial half

theorem actual_value_raw : (value observation nontrivial half : ℝ → ℂ) =ᵐ[volume]
    valueRaw observation nontrivial half :=
  burnolEvenProjection_ae_raw w _ (whole_raw observation nontrivial half)

private theorem raw_gap {x : ℝ} (inside : |x| ≤ q) :
    valueRaw observation nontrivial half x = valueRaw observation nontrivial half 0 := by
  unfold valueRaw
  rw [burnolEvenProjectionRaw_gap_read _ _ (abs_le.mp inside),
    burnolEvenProjectionRaw_gap_read _ _ (by norm_num [symmetricInterval])]

private theorem raw_zero : valueRaw observation nontrivial half 0 = contact observation nontrivial half :=
  burnolEvenProjectionRaw_gap_read _ _ (by norm_num [symmetricInterval])

private theorem forward_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolInnerGapForward (T.outwardRaw coordinate) (-x) =
      burnolInnerGapForward (T.outwardRaw coordinate) x := by
  unfold burnolInnerGapForward
  apply tsum_congr
  intro n
  simp only [neg_div, OriginalWholeDebtRJointMobiusTateRSource.outwardRaw, abs_neg]

private theorem forward_four_gap (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x| ≤ (4 : ℝ)) : burnolInnerGapForward (T.outwardRaw coordinate) x = 0 := by
  unfold burnolInnerGapForward
  have zero (n : ℕ+) : (((n : ℕ) : ℂ)⁻¹) * T.outwardRaw coordinate (x / (n : ℕ)) = 0 := by
    have one : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
    have small : |x / (n : ℕ)| ≤ (4 : ℝ) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℕ)), div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℕ))]
      nlinarith
    rw [T.actual_outward_gap coordinate small, mul_zero]
  simp only [zero, tsum_zero]

private theorem raw_outside {x : ℝ} (outside : q < |x|) :
    valueRaw observation nontrivial half x =
      burnolInnerGapForward (T.outwardRaw coord) x + outerProfile observation nontrivial half |x| := by
  have hx : x ∉ symmetricInterval q := fun h => not_le_of_gt outside (abs_le.mpr h)
  have hn : -x ∉ symmetricInterval q := by simpa only [symmetricInterval, mem_Icc] using
    (show ¬ (-q ≤ -x ∧ -x ≤ q) from fun h => hx ⟨by linarith [h.2], by linarith [h.1]⟩)
  unfold valueRaw burnolEvenProjectionRaw burnolEvenRaw burnolRawCorrectionRaw
  simp only [indicator_of_notMem hx, indicator_of_notMem hn, zero_add]
  change (1 / 2 : ℂ) * (T.actionRaw coord x + T.actionRaw coord (-x)) -
    (1 / 2 : ℂ) * (Constructor.fourierRaw (second observation nontrivial half : Hq) x +
      Constructor.fourierRaw (second observation nontrivial half : Hq) (-x)) = _
  rw [action_even]
  unfold outerProfile OriginalWholeDebtRJointMobiusTateRSource.actionRaw
  have evenTransform : Constructor.fourierRaw (second observation nontrivial half : Hq) x +
      Constructor.fourierRaw (second observation nontrivial half : Hq) (-x) =
      Constructor.fourierRaw (second observation nontrivial half : Hq) |x| +
      Constructor.fourierRaw (second observation nontrivial half : Hq) (-|x|) := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, neg_neg, add_comm]
  rw [evenTransform]
  simp only [OriginalWholeDebtRJointMobiusTateRSource.powerRaw, abs_abs]
  ring

/-- The full M-window is generated solely by the actual power foot and actual B field. -/
theorem actual_window_profile {x : ℝ} (inside : |x| ≤ (4 : ℝ)) :
    valueRaw observation nontrivial half x = if |x| ≤ q then contact observation nontrivial half
      else outerProfile observation nontrivial half |x| := by
  split_ifs with small
  · exact (raw_gap observation nontrivial half small).trans (raw_zero observation nontrivial half)
  · rw [raw_outside observation nontrivial half (lt_of_not_ge small), forward_four_gap coord inside, zero_add]

private theorem outer_c1 : ContDiffOn ℝ 1 (outerProfile observation nontrivial half) (Ioi 0) := by
  intro x positive
  have powerC1 : ContDiffOn ℝ 1 (fun x : ℝ => (x : ℂ) ^ ((coord).value - 1)) (Ioi 0) := by
    apply positive_c1 _ (fun x : ℝ => -(1 - (coord).value) * (x : ℂ) ^ (-((1 - (coord).value) + 1)))
    · intro x hx
      simpa only [show -(1 - (coord).value) = (coord).value - 1 by ring] using burnolMellinTailPower_hasDerivAt (1 - (coord).value) hx
    · intro x hx
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const x
        (-((1 - (coord).value) + 1)) (Or.inr hx.ne'))).continuousWithinAt
  have power := powerC1.contDiffAt (Ioi_mem_nhds positive)
  have fourier := fourier_c1 (second observation nontrivial half : Hq)
  have reflected : ContDiffAt ℝ 1 (fun y : ℝ => Constructor.fourierRaw
      (second observation nontrivial half : Hq) (-y)) x := fourier.contDiffAt.comp x (by fun_prop)
  unfold outerProfile OriginalWholeDebtRJointMobiusTateRSource.powerRaw
  have absLocal : (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ ((coord).value - 1)) =ᶠ[𝓝 x]
      fun y : ℝ => (y : ℂ) ^ ((coord).value - 1) := by
    filter_upwards [Ioi_mem_nhds positive] with y hy
    rw [abs_of_pos hy]
  have absPower : ContDiffAt ℝ 1 (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ ((coord).value - 1)) x :=
    power.congr_of_eventuallyEq absLocal
  exact ((contDiffAt_const.mul absPower).sub
    ((fourier.contDiffAt.add reflected).div_const 2)).contDiffWithinAt

def lower (n : ℕ+) : ℝ := (n : ℕ) * q

def rowWeight (n : ℕ+) (t : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * (outerProfile observation nontrivial half (t⁻¹ / (n : ℕ)) - contact observation nontrivial half)

def rowSlope (n : ℕ+) (t : ℝ) : ℂ :=
  deriv (rowWeight observation nontrivial half n) (max q (min (lower n)⁻¹ t))

def rowSource (n : ℕ+) : BurnolL2 :=
  if lower n < (4 : ℝ) then burnolWeightedReciprocalStepSource q (lower n)⁻¹
    (rowWeight observation nontrivial half n) (rowSlope observation nontrivial half n) else 0

def rowWave (n : ℕ+) : BurnolL2 :=
  if lower n < (4 : ℝ) then burnolWeightedReciprocalStepWave q (lower n)⁻¹
    (rowWeight observation nontrivial half n) (rowSlope observation nontrivial half n) else 0

def inverseSource : BurnolL2 := ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
  FiniteMobiusResolventFlux.coefficient n • rowSource observation nontrivial half n

def paWave : BurnolL2 := ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
  FiniteMobiusResolventFlux.coefficient n • rowWave observation nontrivial half n

private theorem row_bounds (n : ℕ+) : q ≤ lower n ∧ 0 < lower n := by
  have one : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
  unfold lower
  constructor <;> nlinarith

private theorem row_weight_c1 (n : ℕ+) :
    ContDiffOn ℝ 1 (rowWeight observation nontrivial half n) (Ioi 0) := by
  intro t positive
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have moved : ContDiffAt ℝ 1 (fun x : ℝ => x⁻¹ / (n : ℕ)) t :=
    ((contDiffAt_id.inv positive.ne').div_const _)
  have profile := ((outer_c1 observation nontrivial half).contDiffAt
    (Ioi_mem_nhds (div_pos (inv_pos.mpr positive) np))).comp t moved
  unfold rowWeight
  exact (((Complex.ofRealCLM.contDiff.contDiffAt).inv
    (Complex.ofReal_ne_zero.mpr positive.ne')).mul (profile.sub contDiffAt_const)).contDiffWithinAt

private theorem row_slope_continuous (n : ℕ+) (_ordered : lower n < (4 : ℝ)) :
    Continuous (rowSlope observation nontrivial half n) := by
  have regular := (row_weight_c1 observation nontrivial half n).continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  unfold rowSlope
  apply regular.comp_continuous (by fun_prop)
  intro t
  exact (show (0 : ℝ) < q by norm_num).trans_le (le_max_left _ _)

private theorem row_derivative (n : ℕ+) (t : ℝ) (inside : t ∈ Icc q (lower n)⁻¹) :
    HasDerivAt (rowWeight observation nontrivial half n) (rowSlope observation nontrivial half n t) t := by
  have tp : 0 < t := (show (0 : ℝ) < q by norm_num).trans_le inside.1
  have differentiable := ((row_weight_c1 observation nontrivial half n).contDiffAt
    (Ioi_mem_nhds tp)).differentiableAt (by norm_num)
  simpa only [rowSlope, min_eq_right inside.2, max_eq_right inside.1] using differentiable.hasDerivAt

/-- Existing independent Pa closure consumes these actual C1 annulus source weights. -/
theorem actual_pa_wave : paWave observation nontrivial half ∈ burnolOriginalPaInL2 := by
  unfold paWave
  apply Submodule.sum_mem
  intro n slot
  apply Submodule.smul_mem
  unfold rowWave
  split_ifs with ordered
  · have invBounds := inverse_bounds (lower n) 4 (row_bounds n).2 ordered (row_bounds n).1 le_rfl
    exact burnolWeightedReciprocalStepWave_inPa q (lower n)⁻¹ _ _ (by norm_num) invBounds.2
      (row_slope_continuous observation nontrivial half n ordered).continuousOn
  · exact Submodule.zero_mem _

theorem actual_source_action (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (inverseSource observation nontrivial half) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (paWave observation nontrivial half)) test := by
  have row (n : ℕ+) (_slot : n ∈ burnolCenteredMobiusCutoffFinset 4) :
      burnolRemainderSourceRead (rowSource observation nontrivial half n) test =
        (Lp.toTemperedDistributionCLM ℂ volume 2 (rowWave observation nontrivial half n)) test := by
    unfold rowSource rowWave
    split_ifs with ordered
    · have invBounds := inverse_bounds (lower n) 4 (row_bounds n).2 ordered (row_bounds n).1 le_rfl
      exact burnolWeightedReciprocalStepSource_realizes q (lower n)⁻¹ _ _ (by norm_num)
        (by simpa only [show (4 : ℝ)⁻¹ = q by norm_num] using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) (row_bounds n).2).mpr ordered.le)
        invBounds.2.2 (row_slope_continuous observation nontrivial half n ordered).continuousOn test
    · rw [← burnolRemainderSourceReadCLM_apply, map_zero, map_zero]
      rfl
  rw [← burnolRemainderSourceReadCLM_apply test (inverseSource observation nontrivial half)]
  simp_rw [inverseSource, paWave, map_sum, map_smul]
  simp_rw [sum_apply, smul_apply, burnolRemainderSourceReadCLM_apply]
  apply Finset.sum_congr rfl
  intro n slot
  rw [row n slot]

end OriginalWholeDebtRJointMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
