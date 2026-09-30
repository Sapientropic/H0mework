import H0mework.NavierStokes.SourceAction.Dissipation
import H0mework.NavierStokes.SourceAction.Next
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativePositiveTimeMoments

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderEvolution
open NativeFullOrderLimit NativeFullOrderNext NativeFullOrderDissipation

noncomputable section

theorem frequencySize_sq_le_viscous (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    frequencySize wave ^ 2 ≤ 8 * integerWaveViscousMultiplier wave := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate)
    (fun _ => (1 : ℝ)) (fun index => |(wave index : ℝ)|)
  have squared : (∑ index : Coordinate, |(wave index : ℝ)|) ^ 2 ≤ 3 * integerWaveNormSq wave := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs, integerWaveNormSq] using! cauchy
  have lattice := ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity.one_le_integerWaveNormSq wave nonzero
  have factor : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have viscous : integerWaveNormSq wave ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    nlinarith [integerWaveNormSq_nonneg wave]
  unfold frequencySize
  nlinarith [sq_nonneg (1 - ∑ index : Coordinate, |(wave index : ℝ)|)]

theorem energy_succ_le_dissipation (radius order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (state : ComplexVorticityHilbertState) :
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight (order + 1) ceiling) state ≤
      8 * weightedVelocityDissipation (wholeRestartModes radius) (wordWeight order ceiling) state := by
  unfold weightedVelocityEnergy weightedVelocityDissipation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro wave inside
  have nonzero : wave ≠ 0 := fun same =>
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius (same ▸ inside)
  have base : (min (frequencySize wave) ceiling) ^ 2 ≤ 8 * integerWaveViscousMultiplier wave :=
    (pow_le_pow_left₀ (le_min (frequencySize_nonneg wave) nonnegative) (min_le_left _ _) 2).trans
      (frequencySize_sq_le_viscous wave nonzero)
  have weighted := mul_le_mul_of_nonneg_left base (sq_nonneg (wordWeight order ceiling wave))
  have rowNonneg : 0 ≤ complexCoordinateVectorNormSq (finiteStateVelocityCoefficient state wave) := by
    unfold complexCoordinateVectorNormSq
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have total := mul_le_mul_of_nonneg_right weighted rowNonneg
  simpa only [wordWeight, pow_succ, mul_pow, mul_assoc, mul_left_comm, mul_comm] using total

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed] {seed : Seed} {radius : ℕ}

private def E (stage : GeneratedWholeRestartCanonicalStage seed radius) (order : ℕ) (ceiling : ℝ) (time : ℝ) : ℝ :=
  weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time)

private def D (stage : GeneratedWholeRestartCanonicalStage seed radius) (order : ℕ) (ceiling : ℝ) (time : ℝ) : ℝ :=
  weightedVelocityDissipation (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time)

private def A (stage : GeneratedWholeRestartCanonicalStage seed radius) (time : ℝ) : ℝ :=
  finiteStateVelocityMajorant (wholeRestartModes radius) (stage.trajectory time) ^ 2

private theorem E_nonneg (stage : GeneratedWholeRestartCanonicalStage seed radius) (order : ℕ) (ceiling time : ℝ) :
    0 ≤ E stage order ceiling time := by
  unfold E
  rw [← weightedVelocityRead_norm_sq]
  exact sq_nonneg _

private theorem path_continuous (stage : GeneratedWholeRestartCanonicalStage seed radius) :
    ContinuousOn stage.trajectory (Icc 0 (wholeRestartDuration seed)) :=
  HasDerivAt.continuousOn (fun time inside => (stage.physical time inside).1)

private theorem E_continuous (stage : GeneratedWholeRestartCanonicalStage seed radius) (order : ℕ) (ceiling : ℝ) :
    ContinuousOn (E stage order ceiling) (Icc 0 (wholeRestartDuration seed)) := by
  have h := ((weightedVelocityRead (wholeRestartModes radius) (wordWeight order ceiling)).continuous.comp_continuousOn
    (path_continuous stage)).norm.pow 2
  exact h.congr (fun time _ => (weightedVelocityRead_norm_sq (wholeRestartModes radius)
    (wordWeight order ceiling) (stage.trajectory time)).symm)

private theorem D_continuous (stage : GeneratedWholeRestartCanonicalStage seed radius) (order : ℕ) (ceiling : ℝ) :
    ContinuousOn (D stage order ceiling) (Icc 0 (wholeRestartDuration seed)) := by
  unfold D weightedVelocityDissipation complexCoordinateVectorNormSq
  apply continuousOn_finsetSum
  intro wave _
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro coordinate _
  have velocity := (velocityRead wave).continuous.comp_continuousOn (path_continuous stage)
  have row := (continuous_apply coordinate).comp_continuousOn velocity
  exact Complex.continuous_normSq.comp_continuousOn row

private theorem A_continuous (stage : GeneratedWholeRestartCanonicalStage seed radius) :
    ContinuousOn (A stage) (Icc 0 (wholeRestartDuration seed)) := by
  intro time inside
  exact ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt (wholeRestartModes radius)
    stage.trajectory time _ (stage.physical time inside).1).pow 2).continuousWithinAt

private theorem E_deriv_continuous (stage : GeneratedWholeRestartCanonicalStage seed radius) (order : ℕ) (ceiling : ℝ) :
    ContinuousOn (deriv (E stage order ceiling)) (Icc 0 (wholeRestartDuration seed)) := by
  let read := weightedVelocityRead (wholeRestartModes radius) (wordWeight order ceiling)
  have generated := (finiteStateVorticityGenerator_contDiff (wholeRestartModes radius) nu.coeff).continuous.comp_continuousOn
    (path_continuous stage)
  have current := read.continuous.comp_continuousOn (path_continuous stage)
  have tangent := read.continuous.comp_continuousOn generated
  have continuity : ContinuousOn (fun time => (2 : ℝ) *
      inner ℝ (read (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time)))
        (read (stage.trajectory time))) (Icc 0 (wholeRestartDuration seed)) :=
    (tangent.inner current).const_mul (2 : ℝ)
  apply continuity.congr
  intro time inside
  dsimp only [read]
  rw [real_inner_comm, weightedVelocityRead_inner]
  exact (stage_weightedVelocityEnergy_hasDerivAt stage (wordWeight order ceiling) time inside).deriv

private theorem A_integral_le (stage : GeneratedWholeRestartCanonicalStage seed radius)
    {a b : ℝ} (aNonneg : 0 ≤ a) (ordered : a ≤ b) (bLe : b ≤ wholeRestartDuration seed) :
    (∫ time in a..b, A stage time) ≤ wholeRestartVelocityCeiling seed := by
  have integrable : IntervalIntegrable (A stage) volume 0 (wholeRestartDuration seed) :=
    ContinuousOn.intervalIntegrable_of_Icc (wholeRestartDuration_pos seed).le (A_continuous stage)
  exact (intervalIntegral.integral_mono_interval aNonneg ordered bLe
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) integrable).trans stage.uniformScalarBudget.2.2.1

private theorem E_propagates (stage : GeneratedWholeRestartCanonicalStage seed radius) (order : ℕ)
    (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    {a b : ℝ} (aNonneg : 0 ≤ a) (ordered : a ≤ b) (bLe : b ≤ wholeRestartDuration seed) :
    E stage order ceiling b ≤ E stage order ceiling a *
      Real.exp (wordRate order nu * wholeRestartVelocityCeiling seed) := by
  have subset : Icc a b ⊆ Icc (0 : ℝ) (wholeRestartDuration seed) := Icc_subset_Icc aNonneg bLe
  have source := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (fun time inside => stage_weightedVelocityEnergy_action_hasDerivAt stage
      (wordWeight order ceiling) time (subset inside))
    (((A_continuous stage).const_mul (wordRate order nu)).mono subset)
    (fun time _ => finite_action_bound (wholeRestartModes radius) order ceiling nonnegative (stage.trajectory time) nu)
    b ⟨ordered, le_rfl⟩
  rw [intervalIntegral.integral_const_mul] at source
  exact source.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (A_integral_le stage aNonneg ordered bLe)
      (wordRate_nonneg order nu))) (E_nonneg stage order ceiling a))

private theorem E_zero_bound (stage : GeneratedWholeRestartCanonicalStage seed radius) (ceiling time : ℝ)
    (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    E stage 0 ceiling time ≤ puncturedWholeVorticityKineticMass (wholeRestartPhysicalState seed) := by
  have paid := ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure.GeneratedWholeRestartCanonicalStage.kineticMass_le
    stage ⟨time, inside⟩
  rw [puncturedWholeVorticityKineticMass_eq_two_mul_finiteEnergy (wholeRestartModes radius)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube radius) (stage.trajectory time)
    (stage.physical time inside).2.1 (fun wave _ => (stage.physical time inside).2.2.1 wave)] at paid
  simpa [E, weightedVelocityEnergy, wordWeight, finiteStateVorticityKineticEnergy] using paid

private theorem D_integral_le (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    {a b bound : ℝ} (aNonneg : 0 ≤ a) (ordered : a ≤ b) (bLe : b ≤ wholeRestartDuration seed)
    (boundNonneg : 0 ≤ bound) (paid : ∀ time ∈ Icc a b, E stage order ceiling time ≤ bound) :
    (∫ time in a..b, D stage order ceiling time) ≤
      bound * (1 + wordRate order nu * wholeRestartVelocityCeiling seed) / nu.coeff := by
  have subset : Icc a b ⊆ Icc (0 : ℝ) (wholeRestartDuration seed) := Icc_subset_Icc aNonneg bLe
  have intDerivative : IntervalIntegrable (deriv (E stage order ceiling)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc ordered ((E_deriv_continuous stage order ceiling).mono subset)
  have intD : IntervalIntegrable (D stage order ceiling) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc ordered ((D_continuous stage order ceiling).mono subset)
  have intA : IntervalIntegrable (A stage) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc ordered ((A_continuous stage).mono subset)
  have pointwise (time : ℝ) (inside : time ∈ Icc a b) :
      deriv (E stage order ceiling) time + nu.coeff * D stage order ceiling time ≤
        (wordRate order nu * bound) * A stage time := by
    have source := stage_energy_retained_dissipation stage order ceiling nonnegative time (subset inside)
    exact source.trans (by
      change wordRate order nu * A stage time * E stage order ceiling time ≤ _
      calc
        _ ≤ wordRate order nu * A stage time * bound :=
          mul_le_mul_of_nonneg_left (paid time inside) (mul_nonneg (wordRate_nonneg order nu) (sq_nonneg _))
        _ = _ := by ring)
  have integrated := intervalIntegral.integral_mono_on ordered
    (intDerivative.add (intD.const_mul nu.coeff)) (intA.const_mul (wordRate order nu * bound)) pointwise
  have write : (∫ time in a..b, deriv (E stage order ceiling) time) =
      E stage order ceiling b - E stage order ceiling a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ intDerivative
    intro time inside
    have original : time ∈ Icc (0 : ℝ) (wholeRestartDuration seed) :=
      subset (by simpa only [uIcc_of_le ordered] using inside)
    exact (stage_weightedVelocityEnergy_action_hasDerivAt stage
      (wordWeight order ceiling) time original).differentiableAt.hasDerivAt
  rw [intervalIntegral.integral_add intDerivative (intD.const_mul nu.coeff),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, write] at integrated
  have total := integrated.trans (mul_le_mul_of_nonneg_left (A_integral_le stage aNonneg ordered bLe)
    (mul_nonneg (wordRate_nonneg order nu) boundNonneg))
  apply (le_div_iff₀ nu.coeff_pos).mpr
  have initialLe := paid a ⟨le_rfl, ordered⟩
  have terminalNonneg := E_nonneg stage order ceiling b
  nlinarith

private theorem exists_next_energy_time
    (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    {delta bound : ℝ} (deltaPositive : 0 < delta) (deltaLe : delta ≤ wholeRestartDuration seed)
    (boundNonneg : 0 ≤ bound)
    (paid : ∀ time ∈ Icc (delta / 2) delta, E stage order ceiling time ≤ bound) :
    ∃ selected ∈ Icc (delta / 2) delta, E stage (order + 1) ceiling selected ≤
      (8 * (bound * (1 + wordRate order nu * wholeRestartVelocityCeiling seed) / nu.coeff)) / (delta / 2) := by
  have halfPositive : 0 < delta / 2 := half_pos deltaPositive
  have ordered : delta / 2 ≤ delta := by linarith
  have subset : Icc (delta / 2) delta ⊆ Icc (0 : ℝ) (wholeRestartDuration seed) :=
    Icc_subset_Icc halfPositive.le deltaLe
  have intE : IntervalIntegrable (E stage (order + 1) ceiling) volume (delta / 2) delta :=
    ContinuousOn.intervalIntegrable_of_Icc ordered ((E_continuous stage (order + 1) ceiling).mono subset)
  have intD : IntervalIntegrable (D stage order ceiling) volume (delta / 2) delta :=
    ContinuousOn.intervalIntegrable_of_Icc ordered ((D_continuous stage order ceiling).mono subset)
  have integralLe := intervalIntegral.integral_mono_on ordered intE (intD.const_mul 8)
    (fun time _ => energy_succ_le_dissipation radius order ceiling nonnegative (stage.trajectory time))
  rw [intervalIntegral.integral_const_mul] at integralLe
  have total := integralLe.trans (mul_le_mul_of_nonneg_left
    (D_integral_le stage order ceiling nonnegative halfPositive.le ordered deltaLe boundNonneg paid) (by norm_num))
  obtain ⟨selected, selectedMem, average⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) (f := E stage (order + 1) ceiling) (g := fun _ => (1 : ℝ))
    (a := delta / 2) (b := delta)
    (by simpa only [uIcc_of_le ordered] using (E_continuous stage (order + 1) ceiling).mono subset)
    (intervalIntegrable_const) (fun _ _ => zero_le_one)
  refine ⟨selected, by simpa only [uIcc_of_le ordered] using selectedMem, ?_⟩
  apply (le_div_iff₀ halfPositive).mpr
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at average
  rw [show delta - delta / 2 = delta / 2 by ring] at average
  exact average.symm.le.trans total

def positiveTimeBudget (seed : Seed) : ℕ → ℝ → ℝ
  | 0, _ => puncturedWholeVorticityKineticMass (wholeRestartPhysicalState seed)
  | order + 1, delta =>
      (8 * (positiveTimeBudget seed order (delta / 2) *
        (1 + wordRate order nu * wholeRestartVelocityCeiling seed) / nu.coeff) / (delta / 2)) *
          Real.exp (wordRate (order + 1) nu * wholeRestartVelocityCeiling seed)

theorem positiveTimeBudget_nonneg (seed : Seed) (order : ℕ) {delta : ℝ} (deltaPositive : 0 < delta) :
    0 ≤ positiveTimeBudget seed order delta := by
  induction order generalizing delta with
  | zero => exact puncturedWholeVorticityKineticMass_nonneg _
  | succ order previous =>
      have lower := previous (half_pos deltaPositive)
      have rate := wordRate_nonneg order nu
      have source := wholeRestartVelocityCeiling_nonneg seed
      have viscosity := nu.coeff_pos
      dsimp only [positiveTimeBudget]
      positivity

theorem stage_positive_time_energy_bound (order : ℕ) (delta : ℝ) (deltaPositive : 0 < delta)
    (deltaLe : delta ≤ wholeRestartDuration seed)
    (stage : GeneratedWholeRestartCanonicalStage seed radius) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (time : ℝ) (inside : time ∈ Icc delta (wholeRestartDuration seed)) :
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time) ≤
      positiveTimeBudget seed order delta := by
  induction order generalizing delta time with
  | zero => exact E_zero_bound stage ceiling time ⟨deltaPositive.le.trans inside.1, inside.2⟩
  | succ order previous =>
      have halfPositive : 0 < delta / 2 := half_pos deltaPositive
      have halfLe : delta / 2 ≤ wholeRestartDuration seed := by linarith
      have previousBound : ∀ actual ∈ Icc (delta / 2) delta,
          E stage order ceiling actual ≤ positiveTimeBudget seed order (delta / 2) := by
        intro actual actualInside
        exact previous (delta / 2) halfPositive halfLe actual ⟨actualInside.1, actualInside.2.trans deltaLe⟩
      obtain ⟨selected, selectedInside, selectedBound⟩ := exists_next_energy_time stage order ceiling nonnegative
        deltaPositive deltaLe (positiveTimeBudget_nonneg seed order halfPositive) previousBound
      have propagation := E_propagates stage (order + 1) ceiling nonnegative
        (halfPositive.le.trans selectedInside.1) (selectedInside.2.trans inside.1) inside.2
      exact propagation.trans (mul_le_mul_of_nonneg_right selectedBound (Real.exp_pos _).le)

theorem receipt_positive_time_moment_control
    (replay : GeneratedWholeRestartCanonicalReplay seed) (order : ℕ) (delta : ℝ)
    (deltaPositive : 0 < delta) (deltaLe : delta ≤ wholeRestartDuration seed)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) (timeAfter : delta ≤ time.1) :
    Summable (momentDensity order ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time)) ∧
      moment order ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) ≤
        positiveTimeBudget seed order delta := by
  let closure := generatedWholeRestartCriticalClosure replay
  have finiteControl (observed : Finset IntegerWavevector) :
      weightedVelocityEnergy observed (fun wave => frequencySize wave ^ order)
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) ≤
      positiveTimeBudget seed order delta := by
    have originalLimit := closure_weightedVelocityEnergy_tendsto closure observed
      (wordWeight order (frequencyCeiling observed)) time
    have controlled : weightedVelocityEnergy observed (wordWeight order (frequencyCeiling observed))
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) ≤
        positiveTimeBudget seed order delta := by
      apply le_of_tendsto' originalLimit
      intro index
      let stage := replay.current (closure.weakClosure.subsequence index)
      exact (weightedVelocityEnergy_le_of_support observed
        (wholeRestartModes (closure.weakClosure.subsequence index))
        (wordWeight order (frequencyCeiling observed)) (stage.trajectory time.1)
        (stage.physical time.1 time.2).2.1).trans
          (stage_positive_time_energy_bound order delta deltaPositive deltaLe stage
            (frequencyCeiling observed) (frequencyCeiling_nonneg observed) time.1 ⟨timeAfter, time.2.2⟩)
    simpa only [energy_full_on_modes] using controlled
  exact ⟨summable_of_sum_le (momentDensity_nonneg order _) finiteControl,
    Real.tsum_le_of_sum_le (momentDensity_nonneg order _) finiteControl⟩

theorem receipt_positive_momentRegular
    (replay : GeneratedWholeRestartCanonicalReplay seed)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) (positive : 0 < time.1) :
    MomentRegular ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) :=
  fun order => (receipt_positive_time_moment_control replay order time.1 positive time.2.2 time le_rfl).1

theorem next_contact_momentRegular (current : GeneratedWholeRestartCurrent nu) :
    MomentRegular current.nextContact.physicalState :=
  receipt_positive_momentRegular (generatedWholeRestartCanonicalReplay current.contact)
    current.nextContact.time current.nextContact.time_pos

/-- The old cofinal source's exact reentry compiler and chosen contact now
consume positive-time gain; the H1 slice itself is not replaced. -/
theorem cofinal_reentry_contact_momentRegular (initial : GeneratedWholeRestartCurrent nu) :
    MomentRegular (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).contact.physicalState :=
  receipt_positive_momentRegular
    (generatedWholeRestartCanonicalReplay
      ((sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).toWholeRestartPhysicalSeed (ν := nu)))
    (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).contact.time
    (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).contact.time_pos

theorem cofinal_occurrence_next_contact_momentRegular (initial : GeneratedWholeRestartCurrent nu) :
    MomentRegular (generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence initial
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence).contact.physicalState := by
  rw [nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent]
  exact cofinal_reentry_contact_momentRegular initial

theorem macro_next_contact_momentRegular {initial next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu initial next) : MomentRegular next.contact.physicalState := by
  cases step
  exact cofinal_occurrence_next_contact_momentRegular initial

end
end SaturationMonoid.NavierStokes.NativePositiveTimeMoments
