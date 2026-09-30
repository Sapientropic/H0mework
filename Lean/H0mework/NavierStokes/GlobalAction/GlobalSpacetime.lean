import H0mework.NavierStokes.GlobalAction.GlobalJets
import H0mework.NavierStokes.SourceAction.Spacetime

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeOldGlobalSpacetime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderAction NativeFullOrderFlux NativeFullOrderSynthesis NativeTimeJetCarrier
open NativeMixedTimeSpace NativeSpacetimeControl NativeOldGlobalMoments NativeOldGlobalTime

noncomputable section

def factor (horizon : ℝ) : ℝ := horizon / (run stackedShortCurrent 0).duration

theorem factor_pos {horizon : ℝ} (positive : 0 < horizon) : 0 < factor horizon :=
  div_pos positive (run stackedShortCurrent 0).receipt.requestedTimePos

theorem factor_duration (horizon : ℝ) : factor horizon * (run stackedShortCurrent 0).duration = horizon :=
  div_mul_cancel₀ horizon (run stackedShortCurrent 0).receipt.requestedTimePos.ne'

def parameterTime (horizon : ℝ) (positive : 0 < horizon) (time : Time 0) : Icc (0 : ℝ) horizon :=
  ⟨factor horizon * time.1, mul_nonneg (factor_pos positive).le time.2.1,
    (mul_le_mul_of_nonneg_left time.2.2 (factor_pos positive).le).trans_eq (factor_duration horizon)⟩

private theorem density_smul (scalar : ℝ) (order : ℕ) (state : ComplexVorticityHilbertState) :
    velocityMomentDensity order (scalar • state) = fun wave => scalar ^ 2 * velocityMomentDensity order state wave := by
  funext wave
  simp only [velocityMomentDensity, lp.coeFn_smul, Pi.smul_apply, rowSq_real_smul]
  ring

def windowProfile (trajectory : OriginalGlobal) (horizon : ℝ) (positive : 0 < horizon) (order : ℕ) : Profile 0 where
  value time := factor horizon ^ order • NativeOldGlobalJets.jet trajectory order (parameterTime horizon positive time).1
  budget spatialOrder := (factor horizon ^ order) ^ 2 * NativeOldGlobalJets.windowJetBudget trajectory horizon order spatialOrder
  continuous := by
    have source := (NativeOldGlobalJets.window_jet_continuous trajectory horizon order).domRestrict
    have coordinate : Continuous (parameterTime horizon positive) :=
      Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
    exact (source.comp coordinate).const_smul (factor horizon ^ order)
  paid spatialOrder time := by
    rw [density_smul]
    exact (NativeOldGlobalJets.jet_moment_control trajectory horizon order spatialOrder
      (parameterTime horizon positive time)).1.mul_left _
  bound spatialOrder time := by
    rw [density_smul, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (NativeOldGlobalJets.jet_moment_control trajectory horizon order spatialOrder
      (parameterTime horizon positive time)).2 (sq_nonneg _)

theorem windowProfile_read (trajectory : OriginalGlobal) (horizon : ℝ) (positive : 0 < horizon)
    (order : ℕ) (time : Time 0) :
    readProfile (windowProfile trajectory horizon positive order) time.1 =
      factor horizon ^ order • NativeOldGlobalJets.jet trajectory order (factor horizon * time.1) := by
  simp only [readProfile, projIcc_of_mem (run stackedShortCurrent 0).receipt.requestedTimePos.le time.2,
    windowProfile, parameterTime]

theorem windowProfile_evolves (trajectory : OriginalGlobal) (horizon : ℝ) (positive : 0 < horizon)
    (order : ℕ) (time : Time 0) :
    HasDerivWithinAt (readProfile (windowProfile trajectory horizon positive order))
      (readProfile (windowProfile trajectory horizon positive (order + 1)) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent 0).duration) time.1 := by
  have original := NativeOldGlobalJets.jet_hasDerivWithinAt trajectory order (factor horizon * time.1)
    (mul_nonneg (factor_pos positive).le time.2.1)
  have linear : HasDerivWithinAt (fun actual => factor horizon * actual) (factor horizon)
      (Icc (0 : ℝ) (run stackedShortCurrent 0).duration) time.1 := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id time.1).const_mul (factor horizon)).hasDerivWithinAt
  have composed := original.scomp time.1 linear
    (fun actual inside => mul_nonneg (factor_pos positive).le inside.1)
  have scaled := composed.const_smul (factor horizon ^ order)
  rw [windowProfile_read]
  have rate : factor horizon ^ order • (factor horizon •
      NativeOldGlobalJets.jet trajectory (order + 1) (factor horizon * time.1)) =
    factor horizon ^ (order + 1) • NativeOldGlobalJets.jet trajectory (order + 1) (factor horizon * time.1) := by
    rw [smul_smul, pow_succ]
  rw [rate] at scaled
  exact scaled.congr_of_mem (fun actual inside => windowProfile_read trajectory horizon positive order ⟨actual, inside⟩) time.2

def field (trajectory : OriginalGlobal) (pair : Spacetime) : PhysicalSpace :=
  spatialField (velocity trajectory pair.1) pair.2

def window (horizon : ℝ) : Set Spacetime := Icc (0 : ℝ) horizon ×ˢ univ

def halfspace : Set Spacetime := Ici (0 : ℝ) ×ˢ univ

def inverseParameter (horizon : ℝ) (pair : Spacetime) : Spacetime := (pair.1 / factor horizon, pair.2)

theorem inverseParameter_mem (horizon : ℝ) (positive : 0 < horizon) (pair : Spacetime)
    (inside : pair ∈ window horizon) : inverseParameter horizon pair ∈ slab 0 := by
  refine ⟨⟨div_nonneg inside.1.1 (factor_pos positive).le, ?_⟩, trivial⟩
  apply (div_le_iff₀ (factor_pos positive)).mpr
  rw [mul_comm, factor_duration]
  exact inside.1.2

theorem field_window_eq_joint (trajectory : OriginalGlobal) (horizon : ℝ) (positive : 0 < horizon)
    (pair : Spacetime) (inside : pair ∈ window horizon) :
    field trajectory pair = jointField (windowProfile trajectory horizon positive) (inverseParameter horizon pair) := by
  have mapped := inverseParameter_mem horizon positive pair inside
  change spatialField (velocity trajectory pair.1) pair.2 =
    spatialField (readProfile (windowProfile trajectory horizon positive 0) (pair.1 / factor horizon)) pair.2
  rw [windowProfile_read trajectory horizon positive 0 ⟨pair.1 / factor horizon, mapped.1⟩]
  rw [pow_zero, one_smul, mul_div_cancel₀ _ (factor_pos positive).ne', NativeOldGlobalJets.jet_zero]

theorem field_window_contDiffOn (trajectory : OriginalGlobal) (horizon : ℝ) (positive : 0 < horizon) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field trajectory) (window horizon) := by
  have source := joint_contDiffOn (windowProfile trajectory horizon positive)
    (windowProfile_evolves trajectory horizon positive)
  have parameters : ContDiff ℝ (↑(⊤ : ℕ∞)) (inverseParameter horizon) :=
    (contDiff_fst.div_const (factor horizon)).prodMk contDiff_snd
  have composed := source.comp parameters.contDiffOn (inverseParameter_mem horizon positive)
  exact composed.congr (fun pair inside => field_window_eq_joint trajectory horizon positive pair inside)

theorem field_global_contDiffOn (trajectory : OriginalGlobal) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field trajectory) halfspace := by
  intro pair inside
  have positive : 0 < pair.1 + 1 := by have lower : 0 ≤ pair.1 := inside.1; linarith
  have nearby := field_window_contDiffOn trajectory (pair.1 + 1) positive pair ⟨⟨inside.1, by linarith⟩, trivial⟩
  apply nearby.mono_of_mem_nhdsWithin
  have upper : ∀ᶠ sample : Spacetime in 𝓝 pair, sample.1 < pair.1 + 1 :=
    (continuous_fst.tendsto pair) (Iio_mem_nhds (by linarith : pair.1 < pair.1 + 1))
  filter_upwards [upper.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with sample below member
  exact ⟨⟨member.1, below.le⟩, trivial⟩

theorem halfspace_unique : UniqueDiffOn ℝ halfspace :=
  (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ

theorem field_global_spacetime_Lp (trajectory : OriginalGlobal) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ halfspace) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (field trajectory) halfspace) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order (field trajectory) halfspace) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  let differential := iteratedFDerivWithin ℝ order (field trajectory) halfspace
  have continuous : ContinuousOn differential domain :=
    ((field_global_contDiffOn trajectory).continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)) halfspace_unique).mono contained
  obtain ⟨ceiling, ceilingBound⟩ := (compact.image_of_continuousOn continuous.norm).bddAbove
  let budget := max ceiling 0
  have pointBound (point : Spacetime) (inside : point ∈ domain) : ‖differential point‖ ≤ budget :=
    (ceilingBound ⟨point, inside, rfl⟩).trans (le_max_left _ _)
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have aeBound : ∀ᵐ point ∂volume.restrict domain, ‖differential point‖ ≤ budget := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact pointBound point inside
  refine ⟨budget, le_max_right _ _, MemLp.of_bound (continuous.aestronglyMeasurable compact.measurableSet) budget aeBound, ?_⟩
  simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) aeBound

end
end SaturationMonoid.NavierStokes.NativeOldGlobalSpacetime
