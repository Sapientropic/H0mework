import H0mework.Versions.X.NavierStokes.TimeJets.TimeRecursion

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeMixedTimeSpace

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativePhysicalFourier NativeFullOrderAction NativeFullOrderNext NativeFullOrderFlux NativeFullOrderSynthesis
open NativeFullOrderTime NativeHigherTimeJetsSource NativeTimeJetCarrier NativeTimeJetRecursion

noncomputable section

theorem hasDerivWithinAt_tsum_Icc_of_within {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (positive : 0 < T) (field next : ι → ℝ → E) (fieldBound nextBound : ι → ℝ)
    (fieldPaid : Summable fieldBound) (nextPaid : Summable nextBound)
    (fieldContinuous : ∀ index, Continuous (field index)) (nextContinuous : ∀ index, Continuous (next index))
    (evolves : ∀ index time, time ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (field index) (next index time) (Icc (0 : ℝ) T) time)
    (fieldBounded : ∀ index time, time ∈ Icc (0 : ℝ) T → ‖field index time‖ ≤ fieldBound index)
    (nextBounded : ∀ index time, time ∈ Icc (0 : ℝ) T → ‖next index time‖ ≤ nextBound index)
    (time : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun actual => ∑' index, field index actual)
      (∑' index, next index time.1) (Icc (0 : ℝ) T) time.1 := by
  let extend (index : ι) (actual : ℝ) := field index 0 + ∫ sample in 0..actual, next index sample
  have extendEq (index : ι) (sample : Icc (0 : ℝ) T) : extend index sample.1 = field index sample.1 := by
    have primitive := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le sample.2.1
      (fieldContinuous index).continuousOn
      (fun actual inside => (evolves index actual ⟨inside.1.le, inside.2.le.trans sample.2.2⟩).hasDerivAt
        (Icc_mem_nhds inside.1 (inside.2.trans_le sample.2.2)))
      ((nextContinuous index).intervalIntegrable 0 sample.1)
    dsimp only [extend]
    rw [primitive]
    abel
  have extendedDerivative (index : ι) (sample : ℝ) :
      HasDerivAt (extend index) (next index sample) sample :=
    (intervalIntegral.integral_hasDerivAt_right ((nextContinuous index).intervalIntegrable 0 sample)
      (nextContinuous index).aestronglyMeasurable.stronglyMeasurableAtFilter
      (nextContinuous index).continuousAt).const_add (field index 0)
  have original := hasDerivWithinAt_tsum_Icc T positive extend next fieldBound nextBound fieldPaid nextPaid
    (fun index sample _ => extendedDerivative index sample)
    (fun index => (nextContinuous index).continuousOn)
    (fun index sample inside => by rw [extendEq index ⟨sample, inside⟩]; exact fieldBounded index sample inside)
    nextBounded time
  apply original.congr_of_mem _ time.2
  intro sample inside
  rw [clamp_of_mem positive inside]
  exact tsum_congr fun index => (extendEq index ⟨sample, inside⟩).symm

def readProfile {index : ℕ} (profile : Profile index) (actual : ℝ) : ComplexVorticityHilbertState :=
  profile.value (projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual)

theorem profile_square_moments {index : ℕ} (profile : Profile index) (order : ℕ) (actual : ℝ) :
    Summable (fun wave => frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (readProfile profile actual wave)) ∧
      (∑' wave, frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (readProfile profile actual wave)) ≤
        profile.budget order := by
  let time := projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual
  have paid := profile.paid order time
  change Summable (fun wave => (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (profile.value time wave)) at paid
  have bound := profile.bound order time
  unfold velocityMomentDensity at bound
  simpa only [← pow_mul, Nat.mul_comm order 2, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    readProfile, time] using And.intro paid bound

def profileField {index : ℕ} (profile : Profile index) (actual : ℝ) : PhysicalSpace → PhysicalSpace :=
  spatialField (readProfile profile actual)

def profileSpatialBudget {index : ℕ} (profile : Profile index) (order : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ((profile.budget (order + 2) + ∑' wave, decay wave) / 2)

theorem profile_spatial_control {index : ℕ} (profile : Profile index) (actual : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (profileField profile actual) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (profileField profile actual) point‖ ≤ profileSpatialBudget profile order := by
  have moments order := (profile_square_moments profile order actual).1
  refine ⟨spatialField_smooth_of_square _ moments, ?_⟩
  intro order point
  apply (spatialField_bound_of_square _ moments order point).trans
  unfold profileSpatialBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact add_le_add (profile_square_moments profile (order + 2) actual).2 le_rfl

def profileWord {index : ℕ} (profile : Profile index) (order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  iteratedFDeriv ℝ order (profileField profile actual) point directions

theorem profileWord_eq_sum {index : ℕ} (profile : Profile index) (order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (actual : ℝ) :
    profileWord profile order directions point actual =
      ∑' wave, observeWord order directions wave point (readProfile profile actual wave) := by
  have moments order : Summable fun wave => frequencySize wave ^ order * amplitude (readProfile profile actual) wave :=
    summable_moment_of_square _ order (profile_square_moments profile (order + 2) actual).1
  rw [profileWord, profileField, spatialField_word_eq _ moments]
  exact tsum_congr fun _ => rfl

theorem profile_word_decay {index : ℕ} (profile : Profile index) (order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (actual : ℝ) (wave : IntegerWavevector) :
    ‖observeWord order directions wave point (readProfile profile actual wave)‖ ≤
      (wordNorm order directions * Real.sqrt (profile.budget (order + 4))) * decay wave := by
  have paid := profile_square_moments profile (order + 4) actual
  have highPaid : Summable fun wave => (frequencySize wave ^ (order + 4)) ^ 2 *
      complexCoordinateAmplitudeSq (readProfile profile actual wave) := by
    simpa only [← pow_mul, Nat.mul_comm (order + 4) 2] using paid.1
  have highBound : (∑' wave, (frequencySize wave ^ (order + 4)) ^ 2 *
      complexCoordinateAmplitudeSq (readProfile profile actual wave)) ≤ profile.budget (order + 4) := by
    simpa only [← pow_mul, Nat.mul_comm (order + 4) 2] using paid.2
  apply (observeWord_norm_le order directions wave point _).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (weighted_row_decay (fun wave => readProfile profile actual wave) order _ highPaid highBound wave)
    (wordNorm_nonneg order directions)

theorem profileWord_hasDerivWithinAt {index : ℕ} (current next : Profile index)
    (evolves : ∀ time : Time index, HasDerivWithinAt (readProfile current) (readProfile next time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace) (time : Time index) :
    HasDerivWithinAt (profileWord current order directions point) (profileWord next order directions point time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  have source := hasDerivWithinAt_tsum_Icc_of_within _ (run stackedShortCurrent index).receipt.requestedTimePos
    (fun wave actual => observeWord order directions wave point (readProfile current actual wave))
    (fun wave actual => observeWord order directions wave point (readProfile next actual wave))
    (fun wave => (wordNorm order directions * Real.sqrt (current.budget (order + 4))) * decay wave)
    (fun wave => (wordNorm order directions * Real.sqrt (next.budget (order + 4))) * decay wave)
    (decay_summable.mul_left _) (decay_summable.mul_left _)
    (fun wave => (observeWord order directions wave point).continuous.comp
      ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp
        (current.continuous.comp continuous_projIcc)))
    (fun wave => (observeWord order directions wave point).continuous.comp
      ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp
        (next.continuous.comp continuous_projIcc)))
    (fun wave actual inside => (observeWord order directions wave point).hasFDerivAt.comp_hasDerivWithinAt actual
      ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivWithinAt actual
        (evolves ⟨actual, inside⟩)))
    (fun wave actual _ => profile_word_decay current order directions point actual wave)
    (fun wave actual _ => profile_word_decay next order directions point actual wave) time
  rw [← profileWord_eq_sum] at source
  exact source.congr_of_mem (fun actual _ => profileWord_eq_sum current order directions point actual) time.2

theorem profileWord_joint_continuous {index : ℕ} (profile : Profile index) (order : ℕ)
    (directions : Fin order → PhysicalSpace) :
    Continuous (fun pair : ℝ × PhysicalSpace => profileWord profile order directions pair.2 pair.1) := by
  have same : (fun pair : ℝ × PhysicalSpace => profileWord profile order directions pair.2 pair.1) =
      fun pair => ∑' wave, observeWord order directions wave pair.2 (readProfile profile pair.1 wave) :=
    funext fun pair => profileWord_eq_sum profile order directions pair.2 pair.1
  rw [same]
  apply continuous_tsum
  · intro wave
    have reader : Continuous (readProfile profile) := profile.continuous.comp continuous_projIcc
    have scalar : Continuous (wordScalar order directions wave) := by
      unfold wordScalar
      exact ((monomial_smooth wave).continuous.const_mul (Complex.I ^ order)).const_smul
        (∏ rank, phase wave (directions rank))
    change Continuous (fun pair : ℝ × PhysicalSpace => WithLp.toLp 2
      (fun coordinate : Coordinate => (readProfile profile pair.1 wave coordinate * wordScalar order directions wave pair.2).re))
    apply (PiLp.continuous_toLp 2 (fun _ : Coordinate => ℝ)).comp
    apply continuous_pi
    intro coordinate
    have row : Continuous (fun actual : ℝ => readProfile profile actual wave coordinate) :=
      (continuous_apply coordinate).comp
        ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp reader)
    exact Complex.continuous_re.comp ((row.comp continuous_fst).mul (scalar.comp continuous_snd))
  · exact decay_summable.mul_left (wordNorm order directions * Real.sqrt (profile.budget (order + 4)))
  · intro wave pair
    exact profile_word_decay profile order directions pair.2 pair.1 wave

def physicalJet (index timeOrder : ℕ) (actual : ℝ) : PhysicalSpace → PhysicalSpace :=
  profileField (jet index timeOrder) actual

def spatialBudget (index timeOrder spatialOrder : ℕ) : ℝ :=
  profileSpatialBudget (jet index timeOrder) spatialOrder

def mixedWord (index timeOrder spatialOrder : ℕ) (directions : Fin spatialOrder → PhysicalSpace)
    (point : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  profileWord (jet index timeOrder) spatialOrder directions point actual

theorem physicalJet_spatial_control (index timeOrder : ℕ) (actual : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (physicalJet index timeOrder actual) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (physicalJet index timeOrder actual) point‖ ≤
        spatialBudget index timeOrder order := profile_spatial_control (jet index timeOrder) actual

theorem mixedWord_hasDerivWithinAt (index timeOrder spatialOrder : ℕ) (directions : Fin spatialOrder → PhysicalSpace)
    (point : PhysicalSpace) (time : Time index) :
    HasDerivWithinAt (mixedWord index timeOrder spatialOrder directions point)
      (mixedWord index (timeOrder + 1) spatialOrder directions point time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 :=
  profileWord_hasDerivWithinAt (jet index timeOrder) (jet index (timeOrder + 1))
    (jet_hasDerivWithinAt index timeOrder) spatialOrder directions point time

theorem mixedWord_zero (index spatialOrder : ℕ) (directions : Fin spatialOrder → PhysicalSpace) (point : PhysicalSpace) :
    mixedWord index 0 spatialOrder directions point = NativeFullOrderTime.spatialWord index spatialOrder directions point := by
  funext actual
  change iteratedFDeriv ℝ spatialOrder (spatialField (readJet index 0 actual)) point directions = _
  rw [readJet_zero]
  rfl

theorem physicalJet_zero (index : ℕ) (actual : ℝ) :
    physicalJet index 0 actual = spatialField (sourceVelocity index actual) := by
  change spatialField (readJet index 0 actual) = _
  rw [readJet_zero]

theorem mixedWord_iteratedDerivWithin (index timeOrder spatialOrder : ℕ)
    (directions : Fin spatialOrder → PhysicalSpace) (point : PhysicalSpace) (time : Time index) :
    iteratedDerivWithin timeOrder (NativeFullOrderTime.spatialWord index spatialOrder directions point)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 =
        mixedWord index timeOrder spatialOrder directions point time.1 := by
  induction timeOrder generalizing time with
  | zero => rw [iteratedDerivWithin_zero, mixedWord_zero]
  | succ order previous =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun sample inside => previous ⟨sample, inside⟩) (previous time)]
    exact (mixedWord_hasDerivWithinAt index order spatialOrder directions point time).derivWithin
      (uniqueDiffOn_Icc (run stackedShortCurrent index).receipt.requestedTimePos time.1 time.2)

theorem physical_time_derivative (index timeOrder : ℕ) (time : Time index) (point : PhysicalSpace) :
    iteratedDerivWithin timeOrder (fun actual => spatialField (sourceVelocity index actual) point)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 = physicalJet index timeOrder time.1 point := by
  have actual := mixedWord_iteratedDerivWithin index timeOrder 0 (fun n => Fin.elim0 n) point time
  have zeroWord : NativeFullOrderTime.spatialWord index 0 (fun n => Fin.elim0 n) point =
      fun sample => spatialField (sourceVelocity index sample) point := by
    funext sample
    exact iteratedFDeriv_zero_apply _
  rw [zeroWord] at actual
  simpa only [mixedWord, profileWord, physicalJet, iteratedFDeriv_zero_apply] using actual

theorem physical_time_source_agreement (index timeOrder : ℕ) (time : Time index) (point : PhysicalSpace) :
    iteratedDerivWithin timeOrder (fun actual => spatialField (sourceVelocity index actual) point)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 =
        spatialField (iteratedDerivWithin timeOrder (sourceVelocity index)
          (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1) point := by
  rw [physical_time_derivative, sourceVelocity_iteratedDerivWithin]
  rfl

theorem spatialWord_time_contDiffOn (index spatialOrder : ℕ)
    (directions : Fin spatialOrder → PhysicalSpace) (point : PhysicalSpace) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (NativeFullOrderTime.spatialWord index spatialOrder directions point)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro order _ sample inside
  exact ((mixedWord_hasDerivWithinAt index order spatialOrder directions point ⟨sample, inside⟩).congr_of_mem
    (fun actual member => mixedWord_iteratedDerivWithin index order spatialOrder directions point ⟨actual, member⟩)
    inside).differentiableWithinAt

theorem mixed_derivatives_agree (index timeOrder spatialOrder : ℕ)
    (directions : Fin spatialOrder → PhysicalSpace) (point : PhysicalSpace) (time : Time index) :
    iteratedDerivWithin timeOrder (NativeFullOrderTime.spatialWord index spatialOrder directions point)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 =
        iteratedFDeriv ℝ spatialOrder
          (fun space => iteratedDerivWithin timeOrder (fun actual => spatialField (sourceVelocity index actual) space)
            (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1) point directions := by
  have actual : (fun space => iteratedDerivWithin timeOrder
      (fun sample => spatialField (sourceVelocity index sample) space)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1) = physicalJet index timeOrder time.1 :=
    funext fun space => physical_time_derivative index timeOrder time space
  rw [actual, mixedWord_iteratedDerivWithin]
  rfl

theorem profile_spatial_Lp {index : ℕ} (profile : Profile index) (actual : ℝ) (order : ℕ)
    (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (profileField profile actual)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (profileField profile actual)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (profileSpatialBudget profile order) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have source := profile_spatial_control profile actual
  have continuous : Continuous (iteratedFDeriv ℝ order (profileField profile actual)) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) source.1
  have bound : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (profileField profile actual) point‖ ≤ profileSpatialBudget profile order :=
    Eventually.of_forall (source.2 order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ bound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bound⟩

theorem mixed_derivatives_Lp (index timeOrder spatialOrder : ℕ) (time : Time index)
    (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    let field := fun point => iteratedDerivWithin timeOrder
      (fun actual => spatialField (sourceVelocity index actual) point)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1
    MemLp (iteratedFDeriv ℝ spatialOrder field) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ spatialOrder field) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (spatialBudget index timeOrder spatialOrder) * volume domain ^ (1 / exponent.toReal) := by
  dsimp only
  have actual := funext fun point => physical_time_derivative index timeOrder time point
  rw [actual]
  exact profile_spatial_Lp (jet index timeOrder) time.1 spatialOrder exponent compact

end
end SaturationMonoid.NavierStokes.NativeMixedTimeSpace
