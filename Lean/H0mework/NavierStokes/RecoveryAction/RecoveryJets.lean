import H0mework.NavierStokes.SourceAction.PolynomialJets
import H0mework.NavierStokes.RecoveryAction.RecoveryWindow
import H0mework.NavierStokes.RecoveryAction.RecoveryPhysical

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeJets

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeFullOrderAction NativeFullOrderFlux NativeFullOrderSynthesis
open NativeTimeJetCarrier NativeMixedTimeSpace NativeSpacetimeControl
open NativeRecoveryRowAction NativeRecoveryStrongWindow

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {lower upper : ℝ}

def factor (window : ControlledWindow receipt lower upper) : ℝ :=
  (window.last - window.first) / (run stackedShortCurrent 0).duration

theorem factor_pos (window : ControlledWindow receipt lower upper) : 0 < factor window :=
  div_pos (sub_pos.mpr window.ordered) (run stackedShortCurrent 0).receipt.requestedTimePos

theorem factor_duration (window : ControlledWindow receipt lower upper) :
    factor window * (run stackedShortCurrent 0).duration = window.last - window.first :=
  div_mul_cancel₀ _ (run stackedShortCurrent 0).receipt.requestedTimePos.ne'

def parameter (window : ControlledWindow receipt lower upper) (actual : ℝ) : ℝ :=
  window.first + factor window * actual

theorem parameter_mem (window : ControlledWindow receipt lower upper) (time : Time 0) :
    parameter window time.1 ∈ Icc window.first window.last := by
  have after := mul_nonneg (factor_pos window).le time.2.1
  have before := (mul_le_mul_of_nonneg_left time.2.2 (factor_pos window).le).trans_eq (factor_duration window)
  constructor <;> dsimp [parameter] <;> linarith

def parameterTime (window : ControlledWindow receipt lower upper) (time : Time 0) : Icc window.first window.last :=
  ⟨parameter window time.1, parameter_mem window time⟩

def base (window : ControlledWindow receipt lower upper) : Profile 0 where
  value time := velocity receipt (parameter window time.1)
  budget := window.budget
  continuous := by
    have source := window.velocity_continuous.domRestrict
    have coordinates : Continuous (parameterTime window) :=
      Continuous.subtype_mk (continuous_const.add (continuous_const.mul continuous_subtype_val)) _
    exact source.comp coordinates
  paid order time := window.paid order _ (parameter_mem window time)
  bound order time := window.bound order _ (parameter_mem window time)

theorem base_read (window : ControlledWindow receipt lower upper) (time : Time 0) :
    readProfile (base window) time.1 = velocity receipt (parameter window time.1) := by
  simp only [readProfile, projIcc_of_mem (run stackedShortCurrent 0).receipt.requestedTimePos.le time.2, base]

def chartJets (window : ControlledWindow receipt lower upper) : ℕ → Profile 0 :=
  NativePolynomialTimeJets.jet (base window) (factor window * nu.coeff / butterflyGainViscosity.coeff) (factor window)

theorem chart_one (window : ControlledWindow receipt lower upper) (time : Time 0) :
    readProfile (chartJets window 1) time.1 = factor window • rate receipt (parameter window time.1) := by
  apply lp.ext
  funext wave
  rw [show readProfile (chartJets window 1) time.1 wave =
      NativePolynomialTimeJets.read (base window) (factor window * nu.coeff / butterflyGainViscosity.coeff)
        (factor window) 1 time.1 wave from rfl,
    NativePolynomialTimeJets.read_one_row, base_read]
  simp only [lp.coeFn_smul, Pi.smul_apply]
  rw [window.rate_row _ (parameter_mem window time), rateRow, nonlinearRow, smul_sub]
  have coefficient : (factor window * nu.coeff / butterflyGainViscosity.coeff) *
      (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave)) =
      -(factor window * (nu.coeff * integerWaveViscousMultiplier wave)) := by
    field_simp [butterflyGainViscosity.coeff_pos.ne']
  rw [smul_smul, coefficient, neg_smul, smul_smul]
  abel

theorem chart_evolves (window : ControlledWindow receipt lower upper) (order : ℕ) (time : Time 0) :
    HasDerivWithinAt (readProfile (chartJets window order))
      (readProfile (chartJets window (order + 1)) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent 0).duration) time.1 := by
  apply NativePolynomialTimeJets.evolves (base window)
    (factor window * nu.coeff / butterflyGainViscosity.coeff) (factor window) _ order time
  intro actual
  have original := window.velocity_hasDerivWithinAt _ (parameter_mem window actual)
  have coordinate : HasDerivWithinAt (parameter window) (factor window)
      (Icc (0 : ℝ) (run stackedShortCurrent 0).duration) actual.1 := by
    convert! (((hasDerivAt_id actual.1).const_mul (factor window)).const_add window.first).hasDerivWithinAt using 1
    simp only [mul_one]
  have composed := original.scomp actual.1 coordinate (fun sample member => parameter_mem window ⟨sample, member⟩)
  change HasDerivWithinAt (readProfile (base window)) (readProfile (chartJets window 1) actual.1) _ _
  rw [chart_one]
  exact composed.congr_of_mem (fun sample member => base_read window ⟨sample, member⟩) actual.2

def inverse (window : ControlledWindow receipt lower upper) (actual : ℝ) : ℝ :=
  (actual - window.first) / factor window

theorem inverse_mem (window : ControlledWindow receipt lower upper) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) :
    inverse window actual ∈ Icc (0 : ℝ) (run stackedShortCurrent 0).duration := by
  refine ⟨div_nonneg (sub_nonneg.mpr inside.1) (factor_pos window).le, ?_⟩
  apply (div_le_iff₀ (factor_pos window)).mpr
  rw [mul_comm, factor_duration]
  exact sub_le_sub_right inside.2 _

theorem parameter_inverse (window : ControlledWindow receipt lower upper) (actual : ℝ) :
    parameter window (inverse window actual) = actual := by
  unfold parameter inverse
  rw [mul_div_cancel₀ _ (factor_pos window).ne']
  ring

def timeJet (window : ControlledWindow receipt lower upper) (order : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  (factor window)⁻¹ ^ order • readProfile (chartJets window order) (inverse window actual)

def timeJetBudget (window : ControlledWindow receipt lower upper) (order spatialOrder : ℕ) : ℝ :=
  ((factor window)⁻¹ ^ order) ^ 2 * (chartJets window order).budget spatialOrder

theorem timeJet_moment_control (window : ControlledWindow receipt lower upper) (order spatialOrder : ℕ) (actual : ℝ) :
    Summable (velocityMomentDensity spatialOrder (timeJet window order actual)) ∧
      (∑' wave, velocityMomentDensity spatialOrder (timeJet window order actual) wave) ≤
        timeJetBudget window order spatialOrder := by
  let profile := scale ((factor window)⁻¹ ^ order) (chartJets window order)
  let time := projIcc (0 : ℝ) (run stackedShortCurrent 0).duration
    (run stackedShortCurrent 0).receipt.requestedTimePos.le (inverse window actual)
  exact ⟨profile.paid spatialOrder time, profile.bound spatialOrder time⟩

theorem timeJet_zero (window : ControlledWindow receipt lower upper) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) : timeJet window 0 actual = velocity receipt actual := by
  unfold timeJet
  rw [pow_zero, one_smul, show chartJets window 0 = base window from NativePolynomialTimeJets.jet_zero _ _ _,
    base_read window ⟨inverse window actual, inverse_mem window actual inside⟩, parameter_inverse]

theorem timeJet_one (window : ControlledWindow receipt lower upper) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) : timeJet window 1 actual = rate receipt actual := by
  unfold timeJet
  rw [pow_one, chart_one window ⟨inverse window actual, inverse_mem window actual inside⟩,
    parameter_inverse, smul_smul, inv_mul_cancel₀ (factor_pos window).ne', one_smul]

theorem timeJet_evolves (window : ControlledWindow receipt lower upper) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) :
    HasDerivWithinAt (timeJet window order) (timeJet window (order + 1) actual)
      (Icc window.first window.last) actual := by
  have original := chart_evolves window order ⟨inverse window actual, inverse_mem window actual inside⟩
  have coordinate : HasDerivWithinAt (inverse window) (factor window)⁻¹ (Icc window.first window.last) actual := by
    convert! (((hasDerivAt_id actual).sub_const window.first).div_const (factor window)).hasDerivWithinAt using 1
    simp only [one_div]
  have composed := original.scomp actual coordinate (inverse_mem window)
  have scaled := composed.const_smul ((factor window)⁻¹ ^ order)
  convert! scaled using 1
  simp only [timeJet, smul_smul, pow_succ]

theorem velocity_iteratedDerivWithin (window : ControlledWindow receipt lower upper) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) :
    iteratedDerivWithin order (velocity receipt) (Icc window.first window.last) actual = timeJet window order actual := by
  induction order generalizing actual with
  | zero => rw [iteratedDerivWithin_zero]; exact (timeJet_zero window actual inside).symm
  | succ order previous =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (f := timeJet window order)
        (fun sample member => previous sample member) (previous actual inside)]
    exact (timeJet_evolves window order actual inside).derivWithin (uniqueDiffOn_Icc window.ordered actual inside)

theorem velocity_time_contDiffOn (window : ControlledWindow receipt lower upper) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (velocity receipt) (Icc window.first window.last) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro order _ actual inside
  exact ((timeJet_evolves window order actual inside).congr_of_mem
    (fun sample member => velocity_iteratedDerivWithin window order sample member) inside).differentiableWithinAt

def field (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) (pair : Spacetime) : PhysicalSpace :=
  spatialField (velocity receipt pair.1) pair.2

theorem field_receipt (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) (point : PhysicalSpace) :
    field receipt (time.1, point) = spatialField (receipt.wholePath time) point := by
  unfold field
  rw [velocity_on_interval receipt time]

def slab (window : ControlledWindow receipt lower upper) : Set Spacetime := Icc window.first window.last ×ˢ univ

def inverseSpacetime (window : ControlledWindow receipt lower upper) (pair : Spacetime) : Spacetime :=
  (inverse window pair.1, pair.2)

theorem inverseSpacetime_mem (window : ControlledWindow receipt lower upper) (pair : Spacetime)
    (inside : pair ∈ slab window) : inverseSpacetime window pair ∈ NativeSpacetimeControl.slab 0 :=
  ⟨inverse_mem window pair.1 inside.1, trivial⟩

theorem field_eq_joint (window : ControlledWindow receipt lower upper) (pair : Spacetime)
    (inside : pair ∈ slab window) :
    field receipt pair = jointField (chartJets window) (inverseSpacetime window pair) := by
  change spatialField (velocity receipt pair.1) pair.2 = spatialField
    (readProfile (chartJets window 0) (inverse window pair.1)) pair.2
  rw [show chartJets window 0 = base window from NativePolynomialTimeJets.jet_zero _ _ _,
    base_read window ⟨inverse window pair.1, inverse_mem window pair.1 inside.1⟩, parameter_inverse]

theorem field_contDiffOn (window : ControlledWindow receipt lower upper) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field receipt) (slab window) := by
  have source := joint_contDiffOn (chartJets window) (chart_evolves window)
  have coordinates : ContDiff ℝ (↑(⊤ : ℕ∞)) (inverseSpacetime window) :=
    ((contDiff_fst.sub contDiff_const).div_const (factor window)).prodMk contDiff_snd
  exact (source.comp coordinates.contDiffOn (inverseSpacetime_mem window)).congr (field_eq_joint window)

theorem spacetime_frechet_Lp_of_smooth (physicalField : Spacetime → PhysicalSpace) (support : Set Spacetime)
    (smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞)) physicalField support) (unique : UniqueDiffOn ℝ support)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ support) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order physicalField support) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order physicalField support) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  let differential := iteratedFDerivWithin ℝ order physicalField support
  have continuous : ContinuousOn differential domain :=
    (smooth.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)) unique).mono contained
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

theorem field_frechet_Lp (window : ControlledWindow receipt lower upper)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ slab window) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (field receipt) (slab window)) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order (field receipt) (slab window)) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) :=
  spacetime_frechet_Lp_of_smooth _ _ (field_contDiffOn window)
    ((uniqueDiffOn_Icc window.ordered).prod uniqueDiffOn_univ) order exponent compact contained

theorem source_recovery_timeJet_moment_control (initial : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (actual : ℝ) (inside : actual ∈ Icc (sourceWindow initial).first (sourceWindow initial).last) :
    Summable (velocityMomentDensity spatialOrder
      (iteratedDerivWithin timeOrder (velocity (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial))
        (Icc (sourceWindow initial).first (sourceWindow initial).last) actual)) ∧
      (∑' wave, velocityMomentDensity spatialOrder
        (iteratedDerivWithin timeOrder (velocity (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial))
          (Icc (sourceWindow initial).first (sourceWindow initial).last) actual) wave) ≤
            timeJetBudget (sourceWindow initial) timeOrder spatialOrder := by
  rw [velocity_iteratedDerivWithin (sourceWindow initial) timeOrder actual inside]
  exact timeJet_moment_control (sourceWindow initial) timeOrder spatialOrder actual

theorem source_recovery_spacetime_controlled_subinterval (initial : GeneratedWholeRestartCurrent nu) :
    let window := sourceWindow initial
    let physicalField := field (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
    0 < window.first ∧ window.first < window.last ∧
      window.last < (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) physicalField (slab window) ∧
      ∀ order : ℕ, ∀ exponent : ℝ≥0∞, ∀ domain : Set Spacetime, IsCompact domain → domain ⊆ slab window →
        ∃ budget : ℝ, 0 ≤ budget ∧
          MemLp (iteratedFDerivWithin ℝ order physicalField (slab window)) exponent (volume.restrict domain) ∧
          eLpNorm (iteratedFDerivWithin ℝ order physicalField (slab window)) exponent (volume.restrict domain) ≤
            ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  exact ⟨(sourceWindow initial).first_pos, (sourceWindow initial).ordered, (sourceWindow initial).upper_lt,
    field_contDiffOn (sourceWindow initial), fun order exponent _ compact contained =>
      field_frechet_Lp (sourceWindow initial) order exponent compact contained⟩

def absoluteField (initial : GeneratedWholeRestartCurrent nu) (pair : Spacetime) : PhysicalSpace :=
  field (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
    (pair.1 - wholeRestartVelocityAccumulationTime initial, pair.2)

def absoluteSlab (initial : GeneratedWholeRestartCurrent nu) : Set Spacetime :=
  Icc (wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).first)
    (wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).last) ×ˢ univ

theorem absoluteField_receipt (initial : GeneratedWholeRestartCurrent nu)
    (time : Icc (wholeRestartVelocityAccumulationTime initial) (wholeRestartVelocityAccumulationTime initial + 1))
    (point : PhysicalSpace) :
    absoluteField initial (time.1, point) =
      spatialField (sourceGeneratedNativeTemporalAbsoluteWholePath initial time) point := by
  exact field_receipt (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
    (endpointAbsoluteToLocalTime (wholeRestartVelocityAccumulationTime initial) time) point

theorem absoluteField_contDiffOn (initial : GeneratedWholeRestartCurrent nu) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (absoluteField initial) (absoluteSlab initial) := by
  have source := field_contDiffOn (sourceWindow initial)
  have clock : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun pair : Spacetime => (pair.1 - wholeRestartVelocityAccumulationTime initial, pair.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  apply source.comp clock.contDiffOn
  intro pair inside
  refine ⟨?_, trivial⟩
  constructor <;> linarith [inside.1.1, inside.1.2]

theorem source_absolute_recovery_spacetime_controlled_subinterval (initial : GeneratedWholeRestartCurrent nu) :
    let first := wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).first
    let last := wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).last
    wholeRestartVelocityAccumulationTime initial < first ∧ first < last ∧
      last < (sourceGeneratedNativeTemporalSelectedAbsoluteTime initial).1 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (absoluteField initial) (absoluteSlab initial) ∧
      ∀ order : ℕ, ∀ exponent : ℝ≥0∞, ∀ domain : Set Spacetime, IsCompact domain → domain ⊆ absoluteSlab initial →
        ∃ budget : ℝ, 0 ≤ budget ∧
          MemLp (iteratedFDerivWithin ℝ order (absoluteField initial) (absoluteSlab initial)) exponent (volume.restrict domain) ∧
          eLpNorm (iteratedFDerivWithin ℝ order (absoluteField initial) (absoluteSlab initial)) exponent (volume.restrict domain) ≤
            ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  have first := (sourceWindow initial).first_pos
  have ordered := (sourceWindow initial).ordered
  have last := (sourceWindow initial).upper_lt
  refine ⟨by linarith, by linarith, ?_, absoluteField_contDiffOn initial, ?_⟩
  · change wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).last <
      wholeRestartVelocityAccumulationTime initial + (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1
    linarith
  · intro order exponent domain compact contained
    exact spacetime_frechet_Lp_of_smooth _ _ (absoluteField_contDiffOn initial)
      ((uniqueDiffOn_Icc (by linarith :
        wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).first <
        wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).last)).prod uniqueDiffOn_univ)
      order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeJets
