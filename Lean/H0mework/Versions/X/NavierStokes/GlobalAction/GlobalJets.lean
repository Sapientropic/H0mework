import H0mework.Versions.X.NavierStokes.GlobalAction.GlobalTime
import H0mework.Versions.X.NavierStokes.TimeJets.TimeRecursion

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeOldGlobalJets

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderAction NativeFullOrderNext NativeFullOrderFlux NativeFullOrderSynthesis
open NativeFullOrderTime NativeHigherTimeJets NativeHigherTimeJetsSource NativeTimeJetCarrier
open NativeOldGlobalMoments NativeOldGlobalTime

noncomputable section

def actionSequence (state : ComplexVorticityHilbertState) : ℕ → ComplexVorticityHilbertState
  | 0 => state
  | order + 1 => ∑' wave, lp.single 2 wave
      (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • actionSequence state order wave +
        ∑ rank : Fin (order + 1), (order.choose rank : ℝ) • projectedDivergenceCLM wave
          (mixedFlux (actionSequence state rank) (actionSequence state (order - rank)) wave))
termination_by order => order
decreasing_by all_goals omega

theorem actionSequence_receipt (index order : ℕ) (time : Time index) :
    actionSequence (sourceVelocity index time.1) order = NativeTimeJetRecursion.readJet index order time.1 := by
  induction order using Nat.strong_induction_on with
  | h order previous =>
    cases order with
    | zero => rw [actionSequence, NativeTimeJetRecursion.readJet_zero]
    | succ order =>
      rw [actionSequence, ← (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num)
        (NativeTimeJetRecursion.readJet index (order + 1) time.1)).tsum_eq]
      apply tsum_congr
      intro wave
      congr 1
      rw [NativeTimeJetRecursion.readJet_on_interval, NativeTimeJetRecursion.jet_succ_row,
        previous order (by omega), NativeTimeJetRecursion.readJet_on_interval]
      congr 1
      apply Finset.sum_congr rfl
      intro rank _
      rw [previous rank (by omega), previous (order - rank) (by omega),
        NativeTimeJetRecursion.readJet_on_interval, NativeTimeJetRecursion.readJet_on_interval]

def jet (trajectory : OriginalGlobal) (order : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  actionSequence (velocity trajectory actual) order

@[simp] theorem jet_zero (trajectory : OriginalGlobal) : jet trajectory 0 = velocity trajectory := by
  funext actual
  exact actionSequence.eq_1 _

theorem jet_receipt (trajectory : OriginalGlobal) (actual : ℝ) (index : ℕ) (time : Time index)
    (same : trajectory.physicalPath actual = (run stackedShortCurrent index).receipt.wholePath time)
    (order : ℕ) : jet trajectory order actual = NativeTimeJetRecursion.readJet index order time.1 := by
  unfold jet velocity
  rw [same, ← sourceVelocity_on_interval]
  exact actionSequence_receipt index order time

def windowJetBudget (trajectory : OriginalGlobal) (horizon : ℝ) (timeOrder spatialOrder : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (windowIndex trajectory horizon + 1),
    NativeTimeJetRecursion.jetBudget index timeOrder spatialOrder

theorem jet_moment_control (trajectory : OriginalGlobal) (horizon : ℝ) (timeOrder spatialOrder : ℕ)
    (time : Icc (0 : ℝ) horizon) :
    Summable (velocityMomentDensity spatialOrder (jet trajectory timeOrder time.1)) ∧
      (∑' wave, velocityMomentDensity spatialOrder (jet trajectory timeOrder time.1) wave) ≤
        windowJetBudget trajectory horizon timeOrder spatialOrder := by
  obtain ⟨index, bounded, localTime, same⟩ := window_reads_original_receipt trajectory horizon time
  rw [jet_receipt trajectory time.1 index localTime same timeOrder, NativeTimeJetRecursion.readJet_on_interval]
  have source := NativeTimeJetRecursion.jet_moment_control index timeOrder spatialOrder localTime
  refine ⟨source.1, source.2.trans ?_⟩
  exact Finset.single_le_sum
    (fun actual _ => (NativeTimeJetRecursion.jet actual timeOrder).budget_nonneg spatialOrder)
    (Finset.mem_range.mpr bounded)

theorem jet_succ_row (trajectory : OriginalGlobal) (order : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (wave : IntegerWavevector) :
    jet trajectory (order + 1) time wave =
      -(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • jet trajectory order time wave +
        projectedDivergenceCLM wave (mixedTimeSum (jet trajectory) (jet trajectory) order time wave) := by
  obtain ⟨index, _, localTime, same⟩ := window_reads_original_receipt trajectory (time + 1)
    ⟨time, nonnegative, by linarith⟩
  have jets := jet_receipt trajectory time index localTime same
  rw [jets, NativeTimeJetRecursion.readJet_succ_row, jets]
  congr 1
  apply congrArg (projectedDivergenceCLM wave)
  funext output input
  simp only [mixedTimeSum, jets]

theorem jet_one (trajectory : OriginalGlobal) (time : ℝ) (nonnegative : 0 ≤ time) :
    jet trajectory 1 time = rate trajectory time := by
  obtain ⟨index, _, localTime, same⟩ := window_reads_original_receipt trajectory (time + 1)
    ⟨time, nonnegative, by linarith⟩
  rw [jet_receipt trajectory time index localTime same, NativeTimeJetRecursion.readJet_one]
  apply lp.ext
  funext wave
  rw [sourceRate_row, rate_apply trajectory time nonnegative, receipt_momentum_at]
  simp only [rateRow, same]

theorem jet_decay (trajectory : OriginalGlobal) (horizon : ℝ) (timeOrder spatialOrder : ℕ)
    (time : Icc (0 : ℝ) horizon) (wave : IntegerWavevector) :
    frequencySize wave ^ spatialOrder * rowAmplitude (jet trajectory timeOrder time.1 wave) ≤
      Real.sqrt (windowJetBudget trajectory horizon timeOrder (spatialOrder + 4)) * decay wave := by
  have source := jet_moment_control trajectory horizon timeOrder (spatialOrder + 4) time
  apply weighted_row_decay _ spatialOrder _ _ _ wave
  · have paid := source.1
    unfold velocityMomentDensity at paid
    simpa only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  · simpa only [velocityMomentDensity, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using source.2

theorem window_jet_continuous (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ) :
    ContinuousOn (jet trajectory order) (Icc (0 : ℝ) horizon) := by
  induction order using Nat.strong_induction_on with
  | h order previous =>
    cases order with
    | zero =>
      rw [jet_zero]
      intro sample inside
      exact (velocity_hasDerivWithinAt trajectory sample inside.1).continuousWithinAt.mono Icc_subset_Ici_self
    | succ order =>
      have tensorContinuous (wave : IntegerWavevector) :
          ContinuousOn (fun actual => mixedTimeSum (jet trajectory) (jet trajectory) order actual wave)
            (Icc (0 : ℝ) horizon) := by
        apply continuousOn_pi.mpr
        intro output
        apply continuousOn_pi.mpr
        intro input
        unfold mixedTimeSum
        apply continuousOn_finsetSum
        intro rank bounded
        have left := previous rank (by simpa using bounded)
        have right := previous (order - rank) (by omega)
        exact continuousOn_const.mul
          (((mixedFluxCLM wave output input).continuous.comp_continuousOn left).clm_apply right)
      have rowContinuous (wave : IntegerWavevector) :
          ContinuousOn (fun actual => jet trajectory (order + 1) actual wave) (Icc (0 : ℝ) horizon) := by
        have linear := ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp_continuousOn
          (previous order (by omega))).const_smul
            (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave))
        have nonlinear := (projectedDivergenceCLM wave).continuous.comp_continuousOn (tensorContinuous wave)
        exact (linear.add nonlinear).congr (fun actual inside => jet_succ_row trajectory order actual inside.1 wave)
      have generated : ContinuousOn (fun actual => ∑' wave,
          (lp.single 2 wave (jet trajectory (order + 1) actual wave) : ComplexVorticityHilbertState))
          (Icc (0 : ℝ) horizon) := by
        apply continuousOn_tsum
        · intro wave
          exact (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp_continuousOn
            (rowContinuous wave)
        · exact decay_summable.mul_left (Real.sqrt (windowJetBudget trajectory horizon (order + 1) 4))
        · intro wave sample inside
          rw [lp.norm_single (by norm_num)]
          apply (Real.le_sqrt_of_sq_le (complexCoordinateVector_norm_sq_le_amplitudeSq _)).trans
          have actual := jet_decay trajectory horizon (order + 1) 0 ⟨sample, inside⟩ wave
          simp only [pow_zero, one_mul, Nat.zero_add] at actual
          convert! actual using 1
      exact generated.congr (fun actual _ =>
        (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (jet trajectory (order + 1) actual)).tsum_eq.symm)

theorem jet_continuousOn (trajectory : OriginalGlobal) (order : ℕ) :
    ContinuousOn (jet trajectory order) (Ici (0 : ℝ)) := by
  intro sample nonnegative
  have localContinuous := window_jet_continuous trajectory (sample + 1) order sample
    ⟨nonnegative, by linarith⟩
  apply localContinuous.mono_of_mem_nhdsWithin
  have before : Iio (sample + 1) ∈ 𝓝 sample := Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds before] with actual nonneg earlier
  exact ⟨nonneg, earlier.le⟩

private theorem hilbert_hasDerivWithinAt_Ici_of_rows
    (field rate : ℝ → ComplexVorticityHilbertState)
    (fieldContinuous : ContinuousOn field (Ici (0 : ℝ)))
    (rateContinuous : ContinuousOn rate (Ici (0 : ℝ)))
    (rowDerivative : ∀ wave time, 0 ≤ time →
      HasDerivWithinAt (fun actual => field actual wave) (rate time wave) (Ici (0 : ℝ)) time)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    HasDerivWithinAt field (rate time) (Ici (0 : ℝ)) time := by
  let retract (actual : ℝ) : Ici (0 : ℝ) := ⟨max 0 actual, by exact le_max_left (0 : ℝ) actual⟩
  let extendedField (actual : ℝ) := field (retract actual).1
  let extendedRate (actual : ℝ) := rate (retract actual).1
  have retractContinuous : Continuous retract :=
    (continuous_const.max continuous_id).subtype_mk _
  have fieldSame (actual : ℝ) (inside : 0 ≤ actual) : extendedField actual = field actual := by
    simp only [extendedField, retract, max_eq_right inside]
  have rateSame (actual : ℝ) (inside : 0 ≤ actual) : extendedRate actual = rate actual := by
    simp only [extendedRate, retract, max_eq_right inside]
  have point : time ∈ Icc (0 : ℝ) (time + 1) := ⟨nonnegative, by linarith⟩
  have actual := NativeTimeJetRecursion.hilbert_hasDerivWithinAt_of_rows (time + 1)
    extendedField extendedRate (fieldContinuous.domRestrict.comp retractContinuous)
    (rateContinuous.domRestrict.comp retractContinuous)
    (fun wave sample inside => by
      rw [rateSame sample inside.1]
      exact ((rowDerivative wave sample inside.1).mono Icc_subset_Ici_self).congr_of_mem
        (fun value member => congrArg (fun state : ComplexVorticityHilbertState => state wave)
          (fieldSame value member.1)) inside) ⟨time, point⟩
  rw [rateSame time nonnegative] at actual
  apply (actual.congr_of_mem (fun sample inside => (fieldSame sample inside.1).symm) point).mono_of_mem_nhdsWithin
  have before : Iio (time + 1) ∈ 𝓝 time := Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds before] with sample member earlier
  exact ⟨member, earlier.le⟩

theorem jet_hasDerivWithinAt (trajectory : OriginalGlobal) (order : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    HasDerivWithinAt (jet trajectory order) (jet trajectory (order + 1) time) (Ici (0 : ℝ)) time := by
  induction order using Nat.strong_induction_on generalizing time with
  | h order previous =>
    cases order with
    | zero =>
      rw [jet_zero, Nat.zero_add, jet_one trajectory time nonnegative]
      exact velocity_hasDerivWithinAt trajectory time nonnegative
    | succ order =>
      apply hilbert_hasDerivWithinAt_Ici_of_rows _ _ (jet_continuousOn trajectory (order + 1))
        (jet_continuousOn trajectory (order + 1 + 1)) _ time nonnegative
      intro wave sample inside
      have lower (rank : ℕ) (bounded : rank ≤ order) :
          HasDerivWithinAt (jet trajectory rank) (jet trajectory (rank + 1) sample) (Ici (0 : ℝ)) sample :=
        previous rank (by omega) sample inside
      have tensor : HasDerivWithinAt
          (fun actual => mixedTimeSum (jet trajectory) (jet trajectory) order actual wave)
          (mixedTimeSum (jet trajectory) (jet trajectory) (order + 1) sample wave)
          (Ici (0 : ℝ)) sample := by
        apply hasDerivWithinAt_pi.mpr
        intro output
        apply hasDerivWithinAt_pi.mpr
        intro input
        exact mixedTimeSum_hasDerivWithinAt _ _ order _ sample lower lower wave output input
      have linear := ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivWithinAt
        sample (lower order le_rfl)).const_smul
          (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave))
      have nonlinear := (projectedDivergenceCLM wave).hasFDerivAt.comp_hasDerivWithinAt sample tensor
      rw [jet_succ_row trajectory (order + 1) sample inside wave]
      exact (linear.add nonlinear).congr_of_mem
        (fun actual member => jet_succ_row trajectory order actual member wave) inside

theorem jet_hasDerivAt (trajectory : OriginalGlobal) (order : ℕ) (time : ℝ) (positive : 0 < time) :
    HasDerivAt (jet trajectory order) (jet trajectory (order + 1) time) time :=
  (jet_hasDerivWithinAt trajectory order time positive.le).hasDerivAt (Ici_mem_nhds positive)

theorem velocity_iteratedDerivWithin (trajectory : OriginalGlobal) (order : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    iteratedDerivWithin order (velocity trajectory) (Ici (0 : ℝ)) time = jet trajectory order time := by
  induction order generalizing time with
  | zero => rw [iteratedDerivWithin_zero, jet_zero]
  | succ order previous =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (s := Ici (0 : ℝ)) (fun sample inside => previous sample inside) (previous time nonnegative)]
    exact (jet_hasDerivWithinAt trajectory order time nonnegative).derivWithin
      (uniqueDiffOn_Ici (0 : ℝ) time nonnegative)

theorem velocity_iteratedDeriv (trajectory : OriginalGlobal) (order : ℕ) (time : ℝ) (positive : 0 < time) :
    iteratedDeriv order (velocity trajectory) time = jet trajectory order time := by
  induction order generalizing time with
  | zero => rw [iteratedDeriv_zero, jet_zero]
  | succ order previous =>
    rw [iteratedDeriv_succ]
    have near : iteratedDeriv order (velocity trajectory) =ᶠ[𝓝 time] jet trajectory order := by
      filter_upwards [Ioi_mem_nhds positive] with sample inside
      exact previous sample inside
    exact ((jet_hasDerivAt trajectory order time positive).congr_of_eventuallyEq near).deriv

theorem velocity_time_contDiffOn (trajectory : OriginalGlobal) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (velocity trajectory) (Ici (0 : ℝ)) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro order _ sample nonnegative
  exact ((jet_hasDerivWithinAt trajectory order sample nonnegative).congr_of_mem
    (fun actual member => velocity_iteratedDerivWithin trajectory order actual member)
    nonnegative).differentiableWithinAt

theorem velocity_timeJet_moment_control (trajectory : OriginalGlobal) (horizon : ℝ) (timeOrder spatialOrder : ℕ)
    (time : Icc (0 : ℝ) horizon) :
    Summable (velocityMomentDensity spatialOrder
      (iteratedDerivWithin timeOrder (velocity trajectory) (Ici (0 : ℝ)) time.1)) ∧
      (∑' wave, velocityMomentDensity spatialOrder
        (iteratedDerivWithin timeOrder (velocity trajectory) (Ici (0 : ℝ)) time.1) wave) ≤
          windowJetBudget trajectory horizon timeOrder spatialOrder := by
  rw [velocity_iteratedDerivWithin trajectory timeOrder time.1 time.2.1]
  exact jet_moment_control trajectory horizon timeOrder spatialOrder time

end
end SaturationMonoid.NavierStokes.NativeOldGlobalJets
