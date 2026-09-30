import H0mework.Versions.X.NavierStokes.TimeGramAction.RecoveryTimeGramReadout
import H0mework.Versions.X.NavierStokes.SourceAction.ReceiptStrongVelocityWrite
import H0mework.NavierStokes.SourceEstimates.WholeKineticCarrier

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeGramAction

open Set Filter MeasureTheory Matrix
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeEndpointVelocityCarrier NativePhysicalFourier NativePairedCarrierJets NativeReceiptStrongVelocityWrite

noncomputable section

def biotSavartCLM : ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  velocityActionCLM.comp (WholeKineticDecay.weightCLM.restrictScalars ℝ)

theorem biotSavartCLM_apply (state : ComplexVorticityHilbertState) : biotSavartCLM state = wholeBiotSavartVelocityState state := by
  apply lp.ext
  funext wave
  change velocityActionCLM (WholeKineticDecay.weightCLM state) wave = _
  by_cases zero : wave = 0
  · subst wave
    rw [velocityActionCLM_zero]
    simp [wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient, biotSavartVelocityCoefficient]
  · rw [velocityActionCLM_nonzero _ ⟨wave, zero⟩, WholeKineticDecay.weightCLM_row state wave zero]
    have positive := Real.sqrt_pos.mpr (integerWaveViscousMultiplier_pos ⟨wave, zero⟩)
    have scalar : (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
        ((Real.sqrt (integerWaveViscousMultiplier wave))⁻¹ • state wave) = state wave := by
      calc
        _ = Real.sqrt (integerWaveViscousMultiplier wave) •
            ((Real.sqrt (integerWaveViscousMultiplier wave))⁻¹ • state wave) :=
          IsScalarTower.algebraMap_smul ℂ _ _
        _ = state wave := by rw [smul_smul, mul_inv_cancel₀ positive.ne', one_smul]
    rw [scalar]
    rfl

def componentCLM (wave : IntegerWavevector) (coordinate : Coordinate) : ComplexVorticityHilbertState →L[ℝ] ScalarSequence :=
  (shiftedCLM wave coordinate).comp biotSavartCLM

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def field (escape : SourceActionEscape receipt point) (index : ℕ) (wave : IntegerWavevector) (coordinate : Coordinate) (actual : ℝ) : ScalarSequence :=
  componentCLM wave coordinate ((ledger.family.stage (NativeRecoveryEscapeCarrier.radius escape index)).trajectory actual)

def rate (escape : SourceActionEscape receipt point) (index : ℕ) (wave : IntegerWavevector) (coordinate : Coordinate) (actual : ℝ) : ScalarSequence :=
  componentCLM wave coordinate (finiteStateVorticityGenerator (wholeRestartModes (NativeRecoveryEscapeCarrier.radius escape index))
    nu.coeff ((ledger.family.stage (NativeRecoveryEscapeCarrier.radius escape index)).trajectory actual))

theorem field_hasDerivAt (escape : SourceActionEscape receipt point) (index : ℕ) (wave : IntegerWavevector) (coordinate : Coordinate)
    (actual : ℝ) (inside : actual ∈ Icc (0 : ℝ) 1) : HasDerivAt (field escape index wave coordinate) (rate escape index wave coordinate actual) actual :=
  (componentCLM wave coordinate).hasFDerivAt.comp_hasDerivAt actual
    ((ledger.family.stage (NativeRecoveryEscapeCarrier.radius escape index)).physical actual inside).1

theorem field_read (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    field escape index wave coordinate (timeAt escape pointLe index node).1 = NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (node, wave, coordinate)) := by
  apply lp.ext
  funext frequency
  change shifted (biotSavartCLM ((ledger.family.stage (NativeRecoveryEscapeCarrier.radius escape index)).trajectory
      (timeAt escape pointLe index node).1)) wave coordinate frequency =
    wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) (frequency - wave) coordinate
  rw [biotSavartCLM_apply]
  unfold NativeRecoveryTimeGramRaw.velocity
  rw [wholeVelocity_punctured]
  rfl

theorem rate_continuousOn (escape : SourceActionEscape receipt point) (index : ℕ) (wave : IntegerWavevector) (coordinate : Coordinate) :
    ContinuousOn (rate escape index wave coordinate) (Icc (0 : ℝ) 1) := by
  have path : ContinuousOn (ledger.family.stage (NativeRecoveryEscapeCarrier.radius escape index)).trajectory (Icc (0 : ℝ) 1) :=
    fun actual inside => ((ledger.family.stage (NativeRecoveryEscapeCarrier.radius escape index)).physical actual inside).1.continuousAt.continuousWithinAt
  exact (componentCLM wave coordinate).continuous.comp_continuousOn
    ((finiteStateVorticityGenerator_contDiff (wholeRestartModes (NativeRecoveryEscapeCarrier.radius escape index)) nu.coeff).continuous.comp_continuousOn path)

def leftPower (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (wave : IntegerWavevector) (coordinate : Coordinate) (right : Index) (actual : ℝ) : ℂ :=
  inner ℂ (rate escape index wave coordinate actual) (NativeRecoveryTimeGramRaw.vector escape pointLe index right)

def leftWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) (coordinate : Coordinate) (right : Index) : ℂ :=
  ∫ actual in (timeAt escape pointLe index first).1..(timeAt escape pointLe index last).1,
    leftPower escape pointLe index wave coordinate right actual

theorem leftWork_eq (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) (coordinate : Coordinate) (right : Index) :
    leftWork escape pointLe index first last wave coordinate right =
      gram escape pointLe index (.inr (last, wave, coordinate)) right - gram escape pointLe index (.inr (first, wave, coordinate)) right := by
  have included : uIcc (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 ⊆ Icc (0 : ℝ) 1 := by
    exact uIcc_subset_Icc (timeAt escape pointLe index first).2 (timeAt escape pointLe index last).2
  have derivative (actual : ℝ) (inside : actual ∈ uIcc (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1) :
      HasDerivAt (fun sample => inner ℂ (field escape index wave coordinate sample) (NativeRecoveryTimeGramRaw.vector escape pointLe index right))
        (leftPower escape pointLe index wave coordinate right actual) actual := by
    simpa only [leftPower, inner_zero_right, zero_add] using
      (field_hasDerivAt escape index wave coordinate actual (included inside)).inner ℂ (hasDerivAt_const actual (NativeRecoveryTimeGramRaw.vector escape pointLe index right))
  have paid : IntervalIntegrable (leftPower escape pointLe index wave coordinate right) volume
      (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 :=
    (((rate_continuousOn escape index wave coordinate).inner continuousOn_const).mono included).intervalIntegrable
  have write := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative paid
  rw [field_read, field_read] at write
  exact write

theorem source_left_work (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) (right : Index) :
    Tendsto (fun index => leftWork escape pointLe (stress.refinement index) first last wave coordinate right)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (last, wave, coordinate)))
          (NativeRecoveryJointTimeKernel.vector stress pointLe right) -
            inner ℂ (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (first, wave, coordinate)))
              (NativeRecoveryJointTimeKernel.vector stress pointLe right))) := by
  have original := (pairing_tendsto stress pointLe (.inr (last, wave, coordinate)) right).sub
    (pairing_tendsto stress pointLe (.inr (first, wave, coordinate)) right)
  apply original.congr'
  exact Eventually.of_forall fun index => (leftWork_eq escape pointLe (stress.refinement index) first last wave coordinate right).symm

def pairedPower (escape : SourceActionEscape receipt point) (index : ℕ)
    (left right : IntegerWavevector × Coordinate) (actual : ℝ) : ℂ :=
  inner ℂ (field escape index left.1 left.2 actual) (rate escape index right.1 right.2 actual) +
    inner ℂ (rate escape index left.1 left.2 actual) (field escape index right.1 right.2 actual)

def pairedWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (left right : IntegerWavevector × Coordinate) : ℂ :=
  ∫ actual in (timeAt escape pointLe index first).1..(timeAt escape pointLe index last).1,
    pairedPower escape index left right actual

theorem pairedWork_eq (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (left right : IntegerWavevector × Coordinate) :
    pairedWork escape pointLe index first last left right =
      gram escape pointLe index (.inr (last, left)) (.inr (last, right)) -
        gram escape pointLe index (.inr (first, left)) (.inr (first, right)) := by
  have included : uIcc (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 ⊆ Icc (0 : ℝ) 1 :=
    uIcc_subset_Icc (timeAt escape pointLe index first).2 (timeAt escape pointLe index last).2
  have continuous (entry : IntegerWavevector × Coordinate) : ContinuousOn (field escape index entry.1 entry.2) (Icc (0 : ℝ) 1) :=
    fun actual inside => (field_hasDerivAt escape index entry.1 entry.2 actual inside).continuousAt.continuousWithinAt
  have paid : IntervalIntegrable (pairedPower escape index left right) volume
      (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 :=
    ((((continuous left).inner (rate_continuousOn escape index right.1 right.2)).add
      ((rate_continuousOn escape index left.1 left.2).inner (continuous right))).mono included).intervalIntegrable
  have derivative (actual : ℝ) (inside : actual ∈ uIcc (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1) :
      HasDerivAt (fun sample => inner ℂ (field escape index left.1 left.2 sample) (field escape index right.1 right.2 sample))
        (pairedPower escape index left right actual) actual :=
    (field_hasDerivAt escape index left.1 left.2 actual (included inside)).inner ℂ
      (field_hasDerivAt escape index right.1 right.2 actual (included inside))
  have write := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative paid
  rw [field_read, field_read, field_read, field_read] at write
  exact write

theorem source_paired_work (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (left right : IntegerWavevector × Coordinate) :
    Tendsto (fun index => pairedWork escape pointLe (stress.refinement index) first last left right)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (last, left)))
          (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (last, right))) -
            inner ℂ (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (first, left)))
              (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (first, right))))) := by
  have original := (pairing_tendsto stress pointLe (.inr (last, left)) (.inr (last, right))).sub
    (pairing_tendsto stress pointLe (.inr (first, left)) (.inr (first, right)))
  apply original.congr'
  exact Eventually.of_forall fun index => (pairedWork_eq escape pointLe (stress.refinement index) first last left right).symm

theorem source_stress_write (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => -pairedWork escape pointLe (stress.refinement index) first last (wave, output) (0, input))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (NativeRecoveryTimeGramReadout.stressRead stress pointLe last wave output input -
          NativeRecoveryTimeGramReadout.stressRead stress pointLe first wave output input)) := by
  simpa only [NativeRecoveryTimeGramReadout.stressRead, neg_sub, neg_sub_neg] using
    (source_paired_work stress pointLe first last (wave, output) (0, input)).neg

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeGramAction
