import H0mework.NavierStokes.SourceAction.PolynomialJets
import H0mework.NavierStokes.SourceAction.PositiveTime

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeReceiptTimeProfile

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeFullOrderAction NativeFullOrderNext NativeFullOrderSynthesis
open NativeFullOrderTime NativeTimeJetCarrier NativeTimeJetRecursion NativeMixedTimeSpace

noncomputable section

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}

structure Window (receipt : WholeContinuousMildSerrinReceipt nu initial duration) where
  first : ℝ
  last : ℝ
  first_nonnegative : 0 ≤ first
  ordered : first < last
  last_le : last ≤ duration
  budget : ℕ → ℝ
  paid : ∀ order (time : Icc (0 : ℝ) duration), time.1 ∈ Icc first last →
    Summable (momentDensity order (receipt.wholePath time))
  bound : ∀ order (time : Icc (0 : ℝ) duration), time.1 ∈ Icc first last →
    moment order (receipt.wholePath time) ≤ budget order

variable {receipt : WholeContinuousMildSerrinReceipt nu initial duration}

def factor (window : Window receipt) : ℝ :=
  (window.last - window.first) / (run stackedShortCurrent 0).duration

theorem factor_pos (window : Window receipt) : 0 < factor window :=
  div_pos (sub_pos.mpr window.ordered) (run stackedShortCurrent 0).receipt.requestedTimePos

theorem factor_duration (window : Window receipt) :
    factor window * (run stackedShortCurrent 0).duration = window.last - window.first :=
  div_mul_cancel₀ _ (run stackedShortCurrent 0).receipt.requestedTimePos.ne'

def parameter (window : Window receipt) (actual : ℝ) : ℝ := window.first + factor window * actual

theorem parameter_mem (window : Window receipt) (time : Time 0) :
    parameter window time.1 ∈ Icc window.first window.last := by
  have after := mul_nonneg (factor_pos window).le time.2.1
  have before := (mul_le_mul_of_nonneg_left time.2.2 (factor_pos window).le).trans_eq (factor_duration window)
  constructor <;> dsimp [parameter] <;> linarith

def parameterTime (window : Window receipt) (time : Time 0) : Icc (0 : ℝ) duration :=
  ⟨parameter window time.1, window.first_nonnegative.trans (parameter_mem window time).1,
    (parameter_mem window time).2.trans window.last_le⟩

theorem parameter_row (window : Window receipt) (time : Time 0) (wave : IntegerWavevector) :
    receiptVelocityRow receipt wave (parameter window time.1) =
      finiteStateVelocityCoefficient (receipt.wholePath (parameterTime window time)) wave :=
  receipt_velocity_row_eq receipt wave (parameterTime window time)

def base (window : Window receipt) : Profile 0 :=
  assemble (fun time wave => receiptVelocityRow receipt wave (parameter window time.1)) window.budget
    (fun wave => by
      apply continuous_iff_continuousAt.mpr
      intro time
      have coordinates : Continuous (fun sample : Time 0 => parameter window sample.1) :=
        continuous_const.add (continuous_const.mul continuous_subtype_val)
      have source : ContinuousAt (receiptVelocityRow receipt wave) (parameter window time.1) :=
        (receipt_velocity_row_hasDerivAt receipt wave (parameterTime window time)).continuousAt
      exact source.comp (f := fun sample : Time 0 => parameter window sample.1) coordinates.continuousAt)
    (fun order time => by
      have source := window.paid order (parameterTime window time) (parameter_mem window time)
      change Summable (fun wave => (frequencySize wave ^ order) ^ 2 *
        complexCoordinateVectorNormSq (finiteStateVelocityCoefficient (receipt.wholePath (parameterTime window time)) wave)) at source
      change Summable (fun wave => (frequencySize wave ^ order) ^ 2 *
        complexCoordinateVectorNormSq (receiptVelocityRow receipt wave (parameter window time.1)))
      simpa only [parameter_row] using source)
    (fun order time => by
      have source := window.bound order (parameterTime window time) (parameter_mem window time)
      simpa only [rawMoment, parameter_row, moment, momentDensity] using source)

theorem base_read_row (window : Window receipt) (time : Time 0) (wave : IntegerWavevector) :
    readProfile (base window) time.1 wave = receiptVelocityRow receipt wave (parameter window time.1) := by
  simp only [readProfile, projIcc_of_mem (run stackedShortCurrent 0).receipt.requestedTimePos.le time.2,
    base, assemble_row]

theorem base_read (window : Window receipt) (time : Time 0) :
    readProfile (base window) time.1 = wholeBiotSavartVelocityState (receipt.wholePath (parameterTime window time)) := by
  apply lp.ext
  funext wave
  rw [base_read_row]
  exact receipt_velocity_row_eq receipt wave (parameterTime window time)

theorem receipt_momentum_action (time : Icc (0 : ℝ) duration) (wave : IntegerWavevector) :
    receiptMomentumAction receipt wave time.1 =
      projectedDivergenceCLM wave (quadraticFlux (wholeBiotSavartVelocityState (receipt.wholePath time)) wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) • wholeBiotSavartVelocityState (receipt.wholePath time) wave := by
  have same : (actualWholeProjectedTransversePath receipt time.1).1 = receipt.wholePath time := by
    change receipt.wholePath (projIcc (0 : ℝ) _ receipt.requestedTimePos.le time.1) = _
    rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
  rw [receiptMomentumAction, same]
  by_cases nonzero : wave ≠ 0
  · unfold wholeLatticeVorticityFourierTangentAt
    change (biotSavartVelocityCLM wave) (_ - _ • receipt.wholePath time wave) = _
    rw [map_sub, map_smul, biotSavartVelocityCLM_apply]
    rw [← quadraticFlux_biotSavart_action (receipt.wholePath time) (receipt.wholePath_zero_row time)
      (wholePath_transverse receipt time) wave, nativeFluidConstitutiveVorticityAction,
      biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero]
    rfl
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [projectedDivergenceCLM_apply, transverseProjection, integerWaveViscousMultiplier]

def jets (window : Window receipt) : ℕ → Profile 0 :=
  NativePolynomialTimeJets.jet (base window) (factor window * nu.coeff / butterflyGainViscosity.coeff) (factor window)

theorem jet_one_row (window : Window receipt) (time : Time 0) (wave : IntegerWavevector) :
    readProfile (jets window 1) time.1 wave = factor window • receiptMomentumAction receipt wave (parameter window time.1) := by
  have action := receipt_momentum_action (receipt := receipt) (parameterTime window time) wave
  change receiptMomentumAction receipt wave (parameter window time.1) = _ at action
  rw [show readProfile (jets window 1) time.1 wave =
      NativePolynomialTimeJets.read (base window) (factor window * nu.coeff / butterflyGainViscosity.coeff)
        (factor window) 1 time.1 wave from rfl,
    NativePolynomialTimeJets.read_one_row, base_read]
  rw [action, smul_sub]
  have coefficient : (factor window * nu.coeff / butterflyGainViscosity.coeff) *
      (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave)) =
      -(factor window * (nu.coeff * integerWaveViscousMultiplier wave)) := by
    field_simp [butterflyGainViscosity.coeff_pos.ne']
  rw [smul_smul, coefficient, neg_smul, smul_smul]
  abel

theorem jets_evolve (window : Window receipt) (order : ℕ) (time : Time 0) :
    HasDerivWithinAt (readProfile (jets window order)) (readProfile (jets window (order + 1)) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent 0).duration) time.1 := by
  apply NativePolynomialTimeJets.evolves (base window)
    (factor window * nu.coeff / butterflyGainViscosity.coeff) (factor window) _ order time
  intro actual
  apply hilbert_hasDerivWithinAt_of_rows _ _ _
    ((base window).continuous.comp continuous_projIcc)
    (NativePolynomialTimeJets.read_continuous _ _ _ 1) _ actual
  intro wave sample inside
  have coordinate : HasDerivAt (parameter window) (factor window) sample := by
    convert! ((hasDerivAt_id sample).const_mul (factor window)).const_add window.first using 1
    simp only [mul_one]
  have original := (receipt_velocity_row_hasDerivAt receipt wave (parameterTime window ⟨sample, inside⟩)).scomp
    sample coordinate
  change HasDerivWithinAt (fun value => readProfile (base window) value wave)
    (readProfile (jets window 1) sample wave) _ _
  rw [jet_one_row window ⟨sample, inside⟩ wave]
  exact original.hasDerivWithinAt.congr_of_mem
    (fun value member => base_read_row window ⟨value, member⟩ wave) inside

variable {Seed : Type} [WholeRestartPhysicalSeed nu Seed] {seed : Seed}

def positiveWindow (replay : GeneratedWholeRestartCanonicalReplay seed) (delta : ℝ)
    (positive : 0 < delta) (before : delta < wholeRestartDuration seed) :
    Window (generatedWholeRestartWholeContinuousMildSerrinReceipt replay) where
  first := delta
  last := wholeRestartDuration seed
  first_nonnegative := positive.le
  ordered := before
  last_le := le_rfl
  budget order := NativePositiveTimeMoments.positiveTimeBudget seed order delta
  paid order time inside := (NativePositiveTimeMoments.receipt_positive_time_moment_control
    replay order delta positive before.le time inside.1).1
  bound order time inside := (NativePositiveTimeMoments.receipt_positive_time_moment_control
    replay order delta positive before.le time inside.1).2

def regularWindow (replay : GeneratedWholeRestartCanonicalReplay seed)
    (paid : MomentRegular (wholeRestartPhysicalState seed)) :
    Window (generatedWholeRestartWholeContinuousMildSerrinReceipt replay) where
  first := 0
  last := wholeRestartDuration seed
  first_nonnegative := le_rfl
  ordered := wholeRestartDuration_pos seed
  last_le := le_rfl
  budget order := moment order (wholeRestartPhysicalState seed) *
    Real.exp (NativeFullOrderEvolution.wordRate order nu * wholeRestartVelocityCeiling seed)
  paid order time _ := (replay_moment_control replay order (paid order) time).1
  bound order time _ := (replay_moment_control replay order (paid order) time).2

end
end SaturationMonoid.NavierStokes.NativeReceiptTimeProfile
