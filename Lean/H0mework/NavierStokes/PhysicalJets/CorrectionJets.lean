import H0mework.NavierStokes.SourceAction.JetObservation
import H0mework.NavierStokes.TimeJets.TimeRecursion
import H0mework.NavierStokes.PhysicalJets.CorrectionPhysical

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeCorrectionJets

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressCurlAlgebra NativeStressSource NativeHigherTimeJets NativeHigherTimeJetsSource
open NativeFullOrderAction NativeFullOrderFlux
open NativeTimeJetCarrier NativeTimeJetRecursion NativeTimeJetObservation NativeCorrectionTime
open NativeCorrectionPhysical

noncomputable section

def filteredJet (modes : Finset IntegerWavevector) (index order : ℕ) (actual : ℝ) :
    ComplexVorticityHilbertState := complexSharpSupportProjection modes (readJet index order actual)

def stressJet (modes : Finset IntegerWavevector) (index order : ℕ) (actual : ℝ) :
    NativeFluidStressFourierState :=
  (fun wave => if wave ∈ modes then mixedTimeSum (readJet index) (readJet index) order actual wave else 0) -
    mixedTimeSum (filteredJet modes index) (filteredJet modes index) order actual

def actionJet (modes : Finset IntegerWavevector) (index order : ℕ) (actual : ℝ) :
    NativeFluidVorticityTangent := nativeFluidConstitutiveVorticityAction (stressJet modes index order actual)

theorem actionJet_zero (modes : Finset IntegerWavevector) (index : ℕ) (actual : ℝ)
    (wave : IntegerWavevector) :
    actionJet modes index 0 actual wave = nativeTurbulenceCorrectionAt modes (sourceState index actual) wave := by
  have atZero (rows : ℕ → ℝ → ComplexVorticityHilbertState) :
      mixedTimeSum rows rows 0 actual = quadraticFlux (rows 0 actual) := by
    funext wave output input
    simp only [mixedTimeSum, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, one_mul, tsub_zero, mixedFlux_diagonal]
  have tensor : stressJet modes index 0 actual = correctionStress modes (sourceState index actual) := by
    rw [stressJet, atZero, atZero]
    funext wave output input
    simp only [filteredJet, readJet_zero,
      correctionStress, velocity_projection_commutes, sourceState, sourceVelocity, Pi.sub_apply]
    split_ifs <;> rfl
  rw [actionJet, tensor]
  exact correctionStress_action modes _
    ((run stackedShortCurrent index).receipt.wholePath_zero_row _) (wholePath_transverse _ _) wave

theorem stressJet_hasDerivWithinAt (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    HasDerivWithinAt (fun actual => stressJet modes index order actual wave)
      (stressJet modes index (order + 1) time.1 wave)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  have original rank (_ : rank ≤ order) := jet_hasDerivWithinAt index rank time
  have projected rank (_ : rank ≤ order) :
      HasDerivWithinAt (filteredJet modes index rank) (filteredJet modes index (rank + 1) time.1)
        (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
    convert! (projectionCLM modes).hasFDerivAt.comp_hasDerivWithinAt time.1
      (jet_hasDerivWithinAt index rank time) using 1 <;>
      simp only [Function.comp_def, projectionCLM_apply, filteredJet]
    rfl
  apply hasDerivWithinAt_pi.mpr
  intro output
  apply hasDerivWithinAt_pi.mpr
  intro input
  have first := mixedTimeSum_hasDerivWithinAt (readJet index) (readJet index) order _ time.1
    original original wave output input
  have second := mixedTimeSum_hasDerivWithinAt (filteredJet modes index) (filteredJet modes index) order _ time.1
    projected projected wave output input
  by_cases inside : wave ∈ modes
  · convert! first.sub second using 1 <;> simp only [stressJet, Pi.sub_apply, if_pos inside]
    rfl
  · convert! (hasDerivWithinAt_const time.1 (Icc (0 : ℝ) (run stackedShortCurrent index).duration)
      (0 : ℂ)).sub second using 1 <;> simp only [stressJet, Pi.sub_apply, if_neg inside, Pi.zero_apply]
    rfl

theorem actionJet_hasDerivWithinAt (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    HasDerivWithinAt (fun actual => actionJet modes index order actual wave)
      (actionJet modes index (order + 1) time.1 wave)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 :=
  (((fourierCurlCoefficientContinuousLinearMap wave).comp (stressDivergenceCLM wave)).restrictScalars ℝ
    ).hasFDerivAt.comp_hasDerivWithinAt time.1 (stressJet_hasDerivWithinAt modes index order time wave)

theorem native_correction_iteratedDerivWithin (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    iteratedDerivWithin order (fun actual => nativeTurbulenceCorrectionAt modes (sourceState index actual) wave)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 = actionJet modes index order time.1 wave := by
  induction order generalizing time with
  | zero => rw [iteratedDerivWithin_zero, actionJet_zero]
  | succ order previous =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (f := fun sample => actionJet modes index order sample wave)
        (fun sample inside => previous ⟨sample, inside⟩) (previous time)]
    exact (actionJet_hasDerivWithinAt modes index order time wave).derivWithin
      (uniqueDiffOn_Icc (run stackedShortCurrent index).receipt.requestedTimePos time.1 time.2)

def correctionJet (modes : Finset IntegerWavevector) (index order : ℕ) : Profile index :=
  NativeTimeJetCarrier.sum (List.ofFn fun rank : Fin (order + 1) =>
    scale (order.choose rank : ℝ)
      (correctionProfile modes (jet index rank) (jet index (order - rank))))

theorem correctionJet_row (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    (correctionJet modes index order).value time wave = actionJet modes index order time.1 wave := by
  rw [correctionJet, sum_ofFn_value]
  simp only [lp.coeFn_sum, Finset.sum_apply, scale, lp.coeFn_smul, Pi.smul_apply, correctionProfile_row]
  let pair (rank : Fin (order + 1)) : NativeFluidStressFourierState :=
    (fun k => if k ∈ modes then mixedFlux ((jet index rank).value time)
      ((jet index (order - rank)).value time) k else 0) -
      mixedFlux (complexSharpSupportProjection modes ((jet index rank).value time))
        (complexSharpSupportProjection modes ((jet index (order - rank)).value time))
  have tensor : stressJet modes index order time.1 =
      ∑ rank : Fin (order + 1), (order.choose rank : ℝ) • pair rank := by
    funext k output input
    simp only [stressJet, mixedTimeSum, filteredJet, readJet_on_interval, pair,
      Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, Complex.ofReal_natCast]
    rw [Fin.sum_univ_eq_sum_range (fun rank => (order.choose rank : ℂ) *
      ((if k ∈ modes then mixedFlux ((jet index rank).value time)
          ((jet index (order - rank)).value time) k else 0) output input -
        mixedFlux (complexSharpSupportProjection modes ((jet index rank).value time))
          (complexSharpSupportProjection modes ((jet index (order - rank)).value time)) k output input)) (order + 1)]
    by_cases inside : k ∈ modes
    · simp only [if_pos inside, mixedTimeSum, readJet_on_interval, mul_sub, Finset.sum_sub_distrib]
    · simp only [if_neg inside, Pi.zero_apply, zero_sub, mul_neg, Finset.sum_neg_distrib]
  rw [actionJet, tensor, ← wholeStressActionCLM_apply, map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro rank _
  have linear := (wholeStressActionCLM.restrictScalars ℝ).map_smul (order.choose rank : ℝ) (pair rank)
  exact congrFun linear wave |>.symm

private theorem sum_budget {index : ℕ} (profiles : List (Profile index)) (order : ℕ) :
    (NativeTimeJetCarrier.sum profiles).budget order =
      (profiles.map fun profile => profile.budget order).foldr (fun item rest => 2 * item + 2 * rest) 0 := by
  induction profiles with
  | nil => rfl
  | cons head tail previous =>
    change 2 * head.budget order + 2 * (NativeTimeJetCarrier.sum tail).budget order = _
    rw [previous]
    rfl

def correctionJetBudget (index timeOrder spatialOrder : ℕ) : ℝ :=
  (List.ofFn fun rank : Fin (timeOrder + 1) => (timeOrder.choose rank : ℝ) ^ 2 *
    correctionPairBudget (jet index rank) (jet index (timeOrder - rank)) spatialOrder
      ).foldr (fun item rest => 2 * item + 2 * rest) 0

theorem correctionJet_budget (modes : Finset IntegerWavevector) (index timeOrder spatialOrder : ℕ) :
    (correctionJet modes index timeOrder).budget spatialOrder = correctionJetBudget index timeOrder spatialOrder := by
  rw [correctionJet, sum_budget, List.map_ofFn]
  simp only [scale, correctionProfile_budget, correctionJetBudget, Function.comp_def]

theorem native_correction_timeJet_moment_control (modes : Finset IntegerWavevector)
    (index timeOrder spatialOrder : ℕ) (time : Time index) :
    (Summable fun wave => (frequencySize wave ^ spatialOrder) ^ 2 * complexCoordinateAmplitudeSq
      (iteratedDerivWithin timeOrder (fun actual => nativeTurbulenceCorrectionAt modes (sourceState index actual) wave)
        (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1)) ∧
    (∑' wave, (frequencySize wave ^ spatialOrder) ^ 2 * complexCoordinateAmplitudeSq
      (iteratedDerivWithin timeOrder (fun actual => nativeTurbulenceCorrectionAt modes (sourceState index actual) wave)
        (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1)) ≤
      correctionJetBudget index timeOrder spatialOrder := by
  have paid := (correctionJet modes index timeOrder).paid spatialOrder time
  have bound := (correctionJet modes index timeOrder).bound spatialOrder time
  change Summable (fun wave => (frequencySize wave ^ spatialOrder) ^ 2 *
    complexCoordinateVectorNormSq ((correctionJet modes index timeOrder).value time wave)) at paid
  rw [correctionJet_budget] at bound
  simp_rw [native_correction_iteratedDerivWithin]
  simpa only [velocityMomentDensity, correctionJet_row,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using And.intro paid bound

def readCorrection (modes : Finset IntegerWavevector) (index order : ℕ) (actual : ℝ) :
    ComplexVorticityHilbertState :=
  (correctionJet modes index order).value
    (projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual)

theorem readCorrection_on_interval (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) :
    readCorrection modes index order time.1 = (correctionJet modes index order).value time := by
  unfold readCorrection
  rw [projIcc_of_mem (run stackedShortCurrent index).receipt.requestedTimePos.le time.2]

theorem readCorrection_row (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    readCorrection modes index order time.1 wave = actionJet modes index order time.1 wave := by
  rw [readCorrection_on_interval, correctionJet_row]

theorem readCorrection_continuous (modes : Finset IntegerWavevector) (index order : ℕ) :
    Continuous (readCorrection modes index order) :=
  (correctionJet modes index order).continuous.comp continuous_projIcc

theorem readCorrection_hasDerivWithinAt (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) :
    HasDerivWithinAt (readCorrection modes index order) (readCorrection modes index (order + 1) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  apply hilbert_hasDerivWithinAt_of_rows _ _ _ (readCorrection_continuous modes index order)
    (readCorrection_continuous modes index (order + 1)) _ time
  intro wave sample inside
  rw [readCorrection_row modes index (order + 1) ⟨sample, inside⟩]
  exact (actionJet_hasDerivWithinAt modes index order ⟨sample, inside⟩ wave).congr_of_mem
    (fun actual member => readCorrection_row modes index order ⟨actual, member⟩ wave) inside

theorem readCorrection_iteratedDerivWithin (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) :
    iteratedDerivWithin order (readCorrection modes index 0)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 = readCorrection modes index order time.1 := by
  induction order generalizing time with
  | zero => rw [iteratedDerivWithin_zero]
  | succ order previous =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun sample inside => previous ⟨sample, inside⟩) (previous time)]
    exact (readCorrection_hasDerivWithinAt modes index order time).derivWithin
      (uniqueDiffOn_Icc (run stackedShortCurrent index).receipt.requestedTimePos time.1 time.2)

theorem readCorrection_time_contDiffOn (modes : Finset IntegerWavevector) (index : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (readCorrection modes index 0)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro order _ sample inside
  exact ((readCorrection_hasDerivWithinAt modes index order ⟨sample, inside⟩).congr_of_mem
    (fun actual member => readCorrection_iteratedDerivWithin modes index order ⟨actual, member⟩)
    inside).differentiableWithinAt

theorem readCorrection_zero_on_interval (modes : Finset IntegerWavevector) (index : ℕ)
    (time : Time index) :
    readCorrection modes index 0 time.1 =
      correctionState modes ((run stackedShortCurrent index).receipt.wholePath time) := by
  apply lp.ext
  funext wave
  rw [readCorrection_row, actionJet_zero, sourceState_on_interval,
    correctionState_apply modes _ ((run stackedShortCurrent index).receipt.wholePath_zero_row time)]

theorem readCorrection_zero (modes : Finset IntegerWavevector) (index : ℕ) :
    readCorrection modes index 0 = fun actual => correctionState modes (sourceState index actual) := by
  funext actual
  let time := projIcc (0 : ℝ) (run stackedShortCurrent index).duration
    (run stackedShortCurrent index).receipt.requestedTimePos.le actual
  change (correctionJet modes index 0).value time = correctionState modes
    ((run stackedShortCurrent index).receipt.wholePath time)
  rw [← readCorrection_on_interval modes index 0 time, readCorrection_zero_on_interval]

theorem native_correction_hilbert_iteratedDerivWithin (modes : Finset IntegerWavevector) (index order : ℕ)
    (time : Time index) :
    iteratedDerivWithin order (fun actual => correctionState modes (sourceState index actual))
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 = readCorrection modes index order time.1 := by
  rw [← readCorrection_zero]
  exact readCorrection_iteratedDerivWithin modes index order time

theorem native_correction_hilbert_time_contDiffOn (modes : Finset IntegerWavevector) (index : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun actual => correctionState modes (sourceState index actual))
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) := by
  rw [← readCorrection_zero]
  exact readCorrection_time_contDiffOn modes index

end
end SaturationMonoid.NavierStokes.NativeCorrectionJets
