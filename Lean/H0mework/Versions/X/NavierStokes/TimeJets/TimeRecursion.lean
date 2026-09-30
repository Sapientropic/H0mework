import H0mework.Versions.X.NavierStokes.TimeJets.TimeCarrier
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeTimeJetRecursion

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeFullOrderAction NativeFullOrderNext NativeFullOrderFlux NativeFullOrderSynthesis
open NativeFullOrderTime NativeHigherTimeJets NativeHigherTimeJetsSource NativeTimeJetCarrier

noncomputable section

def jet (index : ℕ) : ℕ → Profile index
  | 0 => initial index
  | order + 1 =>
      add (viscous (jet index order))
        (NativeTimeJetCarrier.sum (List.ofFn fun rank : Fin (order + 1) =>
          scale (order.choose rank : ℝ)
            (bilinear (jet index rank) (jet index (order - rank)))))
termination_by order => order
decreasing_by all_goals omega

@[simp] theorem jet_zero (index : ℕ) : jet index 0 = initial index := by rw [jet]

def jetBudget (index order spatialOrder : ℕ) : ℝ := (jet index order).budget spatialOrder

def readJet (index order : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  (jet index order).value
    (projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual)

theorem readJet_on_interval (index order : ℕ) (time : Time index) :
    readJet index order time.1 = (jet index order).value time := by
  unfold readJet
  rw [projIcc_of_mem (run stackedShortCurrent index).receipt.requestedTimePos.le time.2]

theorem readJet_zero (index : ℕ) : readJet index 0 = sourceVelocity index := by
  funext actual
  simp only [readJet, jet_zero, initial, sourceVelocity]

theorem jet_moment_control (index order spatialOrder : ℕ) (time : Time index) :
    Summable (velocityMomentDensity spatialOrder ((jet index order).value time)) ∧
      (∑' wave, velocityMomentDensity spatialOrder ((jet index order).value time) wave) ≤ jetBudget index order spatialOrder :=
  ⟨(jet index order).paid spatialOrder time, (jet index order).bound spatialOrder time⟩

theorem jet_continuous (index order : ℕ) : Continuous (readJet index order) :=
  (jet index order).continuous.comp continuous_projIcc

theorem jet_succ_row (index order : ℕ) (time : Time index) (wave : IntegerWavevector) :
    (jet index (order + 1)).value time wave =
      -(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • (jet index order).value time wave +
        ∑ rank : Fin (order + 1), (order.choose rank : ℝ) • projectedDivergenceCLM wave
          (mixedFlux ((jet index rank).value time) ((jet index (order - rank)).value time) wave) := by
  rw [jet]
  change (viscous (jet index order)).value time wave +
    (NativeTimeJetCarrier.sum (List.ofFn fun rank : Fin (order + 1) =>
      scale (order.choose rank : ℝ) (bilinear (jet index rank) (jet index (order - rank))))).value time wave = _
  rw [viscous_row, sum_ofFn_value]
  simp only [lp.coeFn_sum, Finset.sum_apply, scale, lp.coeFn_smul, Pi.smul_apply, bilinear_row]

theorem readJet_succ_row (index order : ℕ) (actual : ℝ) (wave : IntegerWavevector) :
    readJet index (order + 1) actual wave =
      -(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • readJet index order actual wave +
        projectedDivergenceCLM wave (mixedTimeSum (readJet index) (readJet index) order actual wave) := by
  let time := projIcc (0 : ℝ) (run stackedShortCurrent index).duration
    (run stackedShortCurrent index).receipt.requestedTimePos.le actual
  change (jet index (order + 1)).value time wave = _
  rw [jet_succ_row]
  congr 1
  unfold mixedTimeSum
  have rowSum : (fun output input => ∑ rank ∈ Finset.range (order + 1),
      (order.choose rank : ℂ) * mixedFlux (readJet index rank actual) (readJet index (order - rank) actual) wave output input) =
      ∑ rank : Fin (order + 1), (order.choose rank : ℝ) •
        mixedFlux ((jet index rank).value time) ((jet index (order - rank)).value time) wave := by
    funext output input
    simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_natCast]
    rw [Fin.sum_univ_eq_sum_range (fun rank => (order.choose rank : ℂ) *
      mixedFlux ((jet index rank).value time) ((jet index (order - rank)).value time) wave output input) (order + 1)]
    apply Finset.sum_congr rfl
    intro rank inside
    rfl
  rw [rowSum, map_sum]
  apply Finset.sum_congr rfl
  intro rank _
  exact (projectedDivergenceCLM wave).map_smul (order.choose rank : ℝ) _ |>.symm

theorem hilbert_hasDerivWithinAt_of_rows (duration : ℝ)
    (field rate : ℝ → ComplexVorticityHilbertState)
    (fieldContinuous : Continuous field) (rateContinuous : Continuous rate)
    (rowDerivative : ∀ wave time, time ∈ Icc (0 : ℝ) duration →
      HasDerivWithinAt (fun actual => field actual wave) (rate time wave)
        (Icc (0 : ℝ) duration) time)
    (time : Icc (0 : ℝ) duration) :
    HasDerivWithinAt field (rate time.1) (Icc (0 : ℝ) duration) time.1 := by
  have primitive (terminal : Icc (0 : ℝ) duration) :
      (∫ actual in 0..terminal.1, rate actual) = field terminal.1 - field 0 := by
    apply lp.ext
    funext wave
    let read := lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave
    change read (∫ actual in 0..terminal.1, rate actual) = read (field terminal.1 - field 0)
    rw [← read.intervalIntegral_comp_comm (rateContinuous.intervalIntegrable 0 terminal.1), map_sub]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le terminal.2.1
      (read.continuous.comp fieldContinuous).continuousOn
    · intro sample inside
      exact (rowDerivative wave sample ⟨inside.1.le, inside.2.le.trans terminal.2.2⟩).hasDerivAt
        (Icc_mem_nhds inside.1 (inside.2.trans_le terminal.2.2))
    · exact (read.continuous.comp rateContinuous).intervalIntegrable 0 terminal.1
  have actual := (intervalIntegral.integral_hasDerivAt_right
    (rateContinuous.intervalIntegrable 0 time.1)
    rateContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    rateContinuous.continuousAt).const_add (field 0)
  apply actual.hasDerivWithinAt.congr_of_mem _ time.2
  intro sample inside
  rw [primitive ⟨sample, inside⟩]
  abel

private theorem sourceRate_action (index : ℕ) (time : Time index) (wave : IntegerWavevector) :
    sourceRate index time.1 wave =
      projectedDivergenceCLM wave (quadraticFlux (sourceVelocity index time.1) wave) -
        (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) •
          sourceVelocity index time.1 wave := by
  rw [sourceRate_row, sourceVelocity_on_interval]
  let receipt := (run stackedShortCurrent index).receipt
  let state := receipt.wholePath time
  have same : (actualWholeProjectedTransversePath receipt time.1).1 = state := by
    change receipt.wholePath (projIcc (0 : ℝ) _ receipt.requestedTimePos.le time.1) = _
    rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
  rw [receiptMomentumAction, same]
  by_cases nonzero : wave ≠ 0
  · unfold wholeLatticeVorticityFourierTangentAt
    change (biotSavartVelocityCLM wave) (_ - _ • state wave) = _
    rw [map_sub, map_smul, biotSavartVelocityCLM_apply]
    rw [← quadraticFlux_biotSavart_action state (receipt.wholePath_zero_row time)
      (wholePath_transverse receipt time) wave, nativeFluidConstitutiveVorticityAction,
      biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero]
    rfl
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [projectedDivergenceCLM_apply, transverseProjection, integerWaveViscousMultiplier]

theorem readJet_one (index : ℕ) (time : Time index) :
    readJet index 1 time.1 = sourceRate index time.1 := by
  apply lp.ext
  funext wave
  rw [show 1 = 0 + 1 from rfl, readJet_succ_row, sourceRate_action, readJet_zero]
  have stress : mixedTimeSum (readJet index) (readJet index) 0 time.1 wave =
      quadraticFlux (sourceVelocity index time.1) wave := by
    funext output input
    simp only [mixedTimeSum, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, tsub_zero, one_mul, readJet_zero, mixedFlux_diagonal]
  rw [stress]
  simp only [neg_smul, sub_eq_add_neg, add_comm]

theorem jet_hasDerivWithinAt (index order : ℕ) (time : Time index) :
    HasDerivWithinAt (readJet index order) (readJet index (order + 1) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  induction order using Nat.strong_induction_on generalizing time with
  | h order previous =>
    cases order with
    | zero =>
      rw [readJet_zero, Nat.zero_add, readJet_one]
      exact sourceVelocity_hasDerivWithinAt index time
    | succ order =>
      apply hilbert_hasDerivWithinAt_of_rows _ _ _ (jet_continuous index (order + 1))
        (jet_continuous index (order + 1 + 1)) _ time
      intro wave sample inside
      have lower (rank : ℕ) (bounded : rank ≤ order) :
          HasDerivWithinAt (readJet index rank) (readJet index (rank + 1) sample)
            (Icc (0 : ℝ) (run stackedShortCurrent index).duration) sample :=
        previous rank (by omega) ⟨sample, inside⟩
      have tensor : HasDerivWithinAt
          (fun actual => mixedTimeSum (readJet index) (readJet index) order actual wave)
          (mixedTimeSum (readJet index) (readJet index) (order + 1) sample wave)
          (Icc (0 : ℝ) (run stackedShortCurrent index).duration) sample := by
        apply hasDerivWithinAt_pi.mpr
        intro output
        apply hasDerivWithinAt_pi.mpr
        intro input
        exact mixedTimeSum_hasDerivWithinAt _ _ order _ sample lower lower wave output input
      have linear := ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivWithinAt
        sample (lower order le_rfl)).const_smul
          (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave))
      have nonlinear := (projectedDivergenceCLM wave).hasFDerivAt.comp_hasDerivWithinAt sample tensor
      convert! linear.add nonlinear using 1
      · funext actual
        exact readJet_succ_row index order actual wave
      · exact readJet_succ_row index (order + 1) sample wave

theorem sourceVelocity_iteratedDerivWithin (index order : ℕ) (time : Time index) :
    iteratedDerivWithin order (sourceVelocity index)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 = readJet index order time.1 := by
  induction order generalizing time with
  | zero => rw [iteratedDerivWithin_zero, readJet_zero]
  | succ order previous =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun sample inside => previous ⟨sample, inside⟩) (previous time)]
    exact (jet_hasDerivWithinAt index order time).derivWithin
      (uniqueDiffOn_Icc (run stackedShortCurrent index).receipt.requestedTimePos time.1 time.2)

theorem sourceVelocity_time_contDiffOn (index : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (sourceVelocity index)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro order _ sample inside
  exact ((jet_hasDerivWithinAt index order ⟨sample, inside⟩).congr_of_mem
    (fun actual member => sourceVelocity_iteratedDerivWithin index order ⟨actual, member⟩)
    inside).differentiableWithinAt

theorem sourceVelocity_timeJet_moment_control (index timeOrder spatialOrder : ℕ)
    (time : Time index) :
    Summable (velocityMomentDensity spatialOrder
      (iteratedDerivWithin timeOrder (sourceVelocity index)
        (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1)) ∧
      (∑' wave, velocityMomentDensity spatialOrder
        (iteratedDerivWithin timeOrder (sourceVelocity index)
          (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1) wave) ≤
          jetBudget index timeOrder spatialOrder := by
  rw [sourceVelocity_iteratedDerivWithin, readJet_on_interval]
  exact jet_moment_control index timeOrder spatialOrder time

end
end SaturationMonoid.NavierStokes.NativeTimeJetRecursion
