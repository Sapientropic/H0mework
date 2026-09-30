import H0mework.Versions.X.NavierStokes.SourceAction.Spacetime
import H0mework.Versions.X.NavierStokes.PhysicalJets.CorrectionJets

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativePolynomialObservations

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressCurlAlgebra NativeStressSource NativeHigherTimeJets NativeHigherTimeJetsSource
open NativeTimeJetCarrier NativeTimeJetRecursion NativeTimeJetObservation NativeCorrectionTime
open NativeMixedTimeSpace

noncomputable section

variable {index : ℕ} (family : ℕ → Profile index)

theorem read_on (profile : Profile index) (time : Time index) : readProfile profile time.1 = profile.value time := by
  simp only [readProfile, projIcc_of_mem (run stackedShortCurrent index).receipt.requestedTimePos.le time.2]

def curl (order : ℕ) : Profile index := profileCurl (family order)

def filtered (modes : Finset IntegerWavevector) (order : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  complexSharpSupportProjection modes (readProfile (family order) actual)

def stress (modes : Finset IntegerWavevector) (order : ℕ) (actual : ℝ) : NativeFluidStressFourierState :=
  (fun wave => if wave ∈ modes then mixedTimeSum (fun n => readProfile (family n))
    (fun n => readProfile (family n)) order actual wave else 0) -
    mixedTimeSum (filtered family modes) (filtered family modes) order actual

def action (modes : Finset IntegerWavevector) (order : ℕ) (actual : ℝ) : NativeFluidVorticityTangent :=
  nativeFluidConstitutiveVorticityAction (stress family modes order actual)

def correction (modes : Finset IntegerWavevector) (order : ℕ) : Profile index :=
  NativeTimeJetCarrier.sum (List.ofFn fun rank : Fin (order + 1) =>
    scale (order.choose rank : ℝ) (correctionProfile modes (family rank) (family (order - rank))))

theorem correction_row (modes : Finset IntegerWavevector) (order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    (correction family modes order).value time wave = action family modes order time.1 wave := by
  rw [correction, sum_ofFn_value]
  simp only [lp.coeFn_sum, Finset.sum_apply, scale, lp.coeFn_smul, Pi.smul_apply, correctionProfile_row]
  let pair (rank : Fin (order + 1)) : NativeFluidStressFourierState :=
    (fun k => if k ∈ modes then mixedFlux ((family rank).value time)
      ((family (order - rank)).value time) k else 0) -
      mixedFlux (complexSharpSupportProjection modes ((family rank).value time))
        (complexSharpSupportProjection modes ((family (order - rank)).value time))
  have tensor : stress family modes order time.1 =
      ∑ rank : Fin (order + 1), (order.choose rank : ℝ) • pair rank := by
    funext k output input
    simp only [stress, mixedTimeSum, filtered, read_on, pair,
      Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, Complex.ofReal_natCast]
    rw [Fin.sum_univ_eq_sum_range (fun rank => (order.choose rank : ℂ) *
      ((if k ∈ modes then mixedFlux ((family rank).value time)
          ((family (order - rank)).value time) k else 0) output input -
        mixedFlux (complexSharpSupportProjection modes ((family rank).value time))
          (complexSharpSupportProjection modes ((family (order - rank)).value time)) k output input)) (order + 1)]
    by_cases inside : k ∈ modes
    · simp only [if_pos inside, mixedTimeSum, read_on, mul_sub, Finset.sum_sub_distrib]
    · simp only [if_neg inside, Pi.zero_apply, zero_sub, mul_neg, Finset.sum_neg_distrib]
  rw [action, tensor, ← wholeStressActionCLM_apply, map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro rank _
  exact congrFun ((wholeStressActionCLM.restrictScalars ℝ).map_smul (order.choose rank : ℝ) (pair rank)) wave |>.symm

theorem correction_read_row (modes : Finset IntegerWavevector) (order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    readProfile (correction family modes order) time.1 wave = action family modes order time.1 wave := by
  rw [read_on, correction_row]

theorem correction_zero_row (modes : Finset IntegerWavevector) (time : Time index) (wave : IntegerWavevector) :
    readProfile (correction family modes 0) time.1 wave = nativeFluidConstitutiveVorticityAction
      ((fun k => if k ∈ modes then quadraticFlux (readProfile (family 0) time.1) k else 0) -
        quadraticFlux (complexSharpSupportProjection modes (readProfile (family 0) time.1))) wave := by
  rw [correction_read_row]
  have diagonal (rows : ℕ → ℝ → ComplexVorticityHilbertState) :
      mixedTimeSum rows rows 0 time.1 = quadraticFlux (rows 0 time.1) := by
    funext k output input
    simp only [mixedTimeSum, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, one_mul, tsub_zero, mixedFlux_diagonal]
  rw [action, stress, diagonal, diagonal]
  rfl

private theorem sum_budget (profiles : List (Profile index)) (order : ℕ) :
    (NativeTimeJetCarrier.sum profiles).budget order =
      (profiles.map fun profile => profile.budget order).foldr (fun item rest => 2 * item + 2 * rest) 0 := by
  induction profiles with
  | nil => rfl
  | cons head tail previous =>
    change 2 * head.budget order + 2 * (NativeTimeJetCarrier.sum tail).budget order = _
    rw [previous]
    rfl

def correctionBudget (timeOrder spatialOrder : ℕ) : ℝ :=
  (List.ofFn fun rank : Fin (timeOrder + 1) => (timeOrder.choose rank : ℝ) ^ 2 *
    correctionPairBudget (family rank) (family (timeOrder - rank)) spatialOrder
      ).foldr (fun item rest => 2 * item + 2 * rest) 0

theorem correction_budget (modes : Finset IntegerWavevector) (timeOrder spatialOrder : ℕ) :
    (correction family modes timeOrder).budget spatialOrder = correctionBudget family timeOrder spatialOrder := by
  rw [correction, sum_budget, List.map_ofFn]
  simp only [scale, correctionProfile_budget, correctionBudget, Function.comp_def]

variable (evolves : ∀ order time, HasDerivWithinAt (readProfile (family order))
  (readProfile (family (order + 1)) time.1) (Icc (0 : ℝ) (run stackedShortCurrent index).duration) (time : Time index).1)

include evolves in
theorem curl_evolves (order : ℕ) (time : Time index) :
    HasDerivWithinAt (readProfile (curl family order)) (readProfile (curl family (order + 1)) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  apply hilbert_hasDerivWithinAt_of_rows _ (readProfile (curl family order)) (readProfile (curl family (order + 1)))
    ((curl family order).continuous.comp continuous_projIcc)
    ((curl family (order + 1)).continuous.comp continuous_projIcc) _ time
  intro wave sample inside
  have row := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave
    ).hasFDerivAt.comp_hasDerivWithinAt sample (evolves order ⟨sample, inside⟩)
  convert! ((fourierCurlCoefficientContinuousLinearMap wave).restrictScalars ℝ
    ).hasFDerivAt.comp_hasDerivWithinAt sample row using 1

include evolves in
theorem stress_evolves (modes : Finset IntegerWavevector) (order : ℕ) (time : Time index) (wave : IntegerWavevector) :
    HasDerivWithinAt (fun actual => stress family modes order actual wave) (stress family modes (order + 1) time.1 wave)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  have original rank (_ : rank ≤ order) := evolves rank time
  have projected rank (_ : rank ≤ order) :
      HasDerivWithinAt (filtered family modes rank) (filtered family modes (rank + 1) time.1)
        (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
    convert! (projectionCLM modes).hasFDerivAt.comp_hasDerivWithinAt time.1 (evolves rank time) using 1
    · funext actual
      exact (projectionCLM_apply modes _).symm
    · exact (projectionCLM_apply modes _).symm
  apply hasDerivWithinAt_pi.mpr
  intro output
  apply hasDerivWithinAt_pi.mpr
  intro input
  have first := mixedTimeSum_hasDerivWithinAt (fun n => readProfile (family n))
    (fun n => readProfile (family n)) order _ time.1 original original wave output input
  have second := mixedTimeSum_hasDerivWithinAt (filtered family modes) (filtered family modes) order _ time.1
    projected projected wave output input
  by_cases inside : wave ∈ modes
  · convert! first.sub second using 1 <;> simp only [stress, Pi.sub_apply, if_pos inside]
    rfl
  · convert! (hasDerivWithinAt_const time.1 (Icc (0 : ℝ) (run stackedShortCurrent index).duration)
      (0 : ℂ)).sub second using 1 <;> simp only [stress, Pi.sub_apply, if_neg inside, Pi.zero_apply]
    rfl

include evolves in
theorem correction_evolves (modes : Finset IntegerWavevector) (order : ℕ) (time : Time index) :
    HasDerivWithinAt (readProfile (correction family modes order)) (readProfile (correction family modes (order + 1)) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  apply hilbert_hasDerivWithinAt_of_rows _ (readProfile (correction family modes order))
    (readProfile (correction family modes (order + 1)))
    ((correction family modes order).continuous.comp continuous_projIcc)
    ((correction family modes (order + 1)).continuous.comp continuous_projIcc) _ time
  intro wave sample inside
  rw [correction_read_row family modes (order + 1) ⟨sample, inside⟩]
  have actual : HasDerivWithinAt (fun time => action family modes order time wave)
      (action family modes (order + 1) sample wave) (Icc (0 : ℝ) (run stackedShortCurrent index).duration) sample :=
    (((fourierCurlCoefficientContinuousLinearMap wave).comp (stressDivergenceCLM wave)).restrictScalars ℝ
      ).hasFDerivAt.comp_hasDerivWithinAt sample (stress_evolves family evolves modes order ⟨sample, inside⟩ wave)
  exact actual.congr_of_mem
    (fun time member => correction_read_row family modes order ⟨time, member⟩ wave) inside

end
end SaturationMonoid.NavierStokes.NativePolynomialObservations
