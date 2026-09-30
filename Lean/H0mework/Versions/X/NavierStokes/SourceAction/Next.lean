import H0mework.Versions.X.NavierStokes.SourceAction.Evolution

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeFullOrderNext

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderEvolution

noncomputable section

def momentDensity (order : ℕ) (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
    (finiteStateVelocityCoefficient state wave)

def moment (order : ℕ) (state : ComplexVorticityHilbertState) : ℝ := ∑' wave, momentDensity order state wave

def MomentRegular (state : ComplexVorticityHilbertState) : Prop :=
  ∀ order : ℕ, Summable (momentDensity order state)

theorem momentDensity_nonneg (order : ℕ) (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    0 ≤ momentDensity order state wave := by
  apply mul_nonneg (sq_nonneg _)
  unfold complexCoordinateVectorNormSq
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed] {seed : Seed}

/-- The original initial projection reads its budget from the whole source
moment, so no additional per-radius input survives downstream. -/
theorem stage_initial_moment_le
    (replay : GeneratedWholeRestartCanonicalReplay seed) (order : ℕ)
    (paid : Summable (momentDensity order (wholeRestartPhysicalState seed))) (radius : ℕ) :
    weightedVelocityEnergy (wholeRestartModes radius) (fun wave => frequencySize wave ^ order)
      ((replay.current radius).trajectory 0) ≤ moment order (wholeRestartPhysicalState seed) := by
  rw [(replay.current radius).initial]
  change weightedVelocityEnergy (wholeRestartModes radius) (fun wave => frequencySize wave ^ order)
    (complexSharpSupportProjection (wholeRestartModes radius) (wholeRestartPhysicalState seed)) ≤ _
  have projectionRead :
      weightedVelocityEnergy (wholeRestartModes radius) (fun wave => frequencySize wave ^ order)
        (complexSharpSupportProjection (wholeRestartModes radius) (wholeRestartPhysicalState seed)) =
      ∑ wave ∈ wholeRestartModes radius, momentDensity order (wholeRestartPhysicalState seed) wave := by
    unfold weightedVelocityEnergy momentDensity
    apply Finset.sum_congr rfl
    intro wave inside
    simp only [finiteStateVelocityCoefficient, complexSharpSupportProjection_apply, if_pos inside]
  rw [projectionRead]
  exact paid.sum_le_tsum (wholeRestartModes radius)
    (fun wave _ => momentDensity_nonneg order (wholeRestartPhysicalState seed) wave)

theorem replay_moment_control
    (replay : GeneratedWholeRestartCanonicalReplay seed) (order : ℕ)
    (paid : Summable (momentDensity order (wholeRestartPhysicalState seed)))
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    Summable (momentDensity order ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time)) ∧
      moment order ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) ≤
        moment order (wholeRestartPhysicalState seed) *
          Real.exp (wordRate order nu * wholeRestartVelocityCeiling seed) :=
  generated_receipt_full_energy_bound replay order (moment order (wholeRestartPhysicalState seed))
    (stage_initial_moment_le replay order paid) time

theorem replay_momentRegular
    (replay : GeneratedWholeRestartCanonicalReplay seed)
    (paid : MomentRegular (wholeRestartPhysicalState seed))
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    MomentRegular ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) :=
  fun order => (replay_moment_control replay order (paid order) time).1

theorem nextReceipt_moment_control
    (current : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (paid : Summable (momentDensity order current.contact.physicalState))
    (time : Icc (0 : ℝ) (wholeRestartDuration current.contact)) :
    Summable (momentDensity order (current.nextReceipt.wholePath time)) ∧
      moment order (current.nextReceipt.wholePath time) ≤
        moment order current.contact.physicalState *
          Real.exp (wordRate order nu * wholeRestartVelocityCeiling current.contact) :=
  replay_moment_control (generatedWholeRestartCanonicalReplay current.contact) order paid time

theorem next_momentRegular
    (current : GeneratedWholeRestartCurrent nu) (paid : MomentRegular current.contact.physicalState) :
    MomentRegular current.next.contact.physicalState :=
  fun order => (nextReceipt_moment_control current order (paid order) current.nextContact.time).1

/-- Each factor is emitted by the exact next-receipt source in the old run. -/
def runMomentBudget (order : ℕ) : ℕ → ℝ
  | 0 => stackedMomentBudget order
  | index + 1 => runMomentBudget order index * Real.exp
      (wordRate order butterflyGainViscosity * wholeRestartVelocityCeiling
        (run stackedShortCurrent index).contact)

theorem run_contact_moment_control (order index : ℕ) :
    Summable (momentDensity order (run stackedShortCurrent index).contact.physicalState) ∧
      moment order (run stackedShortCurrent index).contact.physicalState ≤ runMomentBudget order index := by
  induction index with
  | zero => exact stacked_contact_all_moments order
  | succ index previous =>
      have actual := nextReceipt_moment_control (run stackedShortCurrent index) order previous.1
        (run stackedShortCurrent index).nextContact.time
      refine ⟨actual.1, actual.2.trans ?_⟩
      exact mul_le_mul_of_nonneg_right previous.2 (Real.exp_pos _).le

theorem run_contact_momentRegular (index : ℕ) :
    MomentRegular (run stackedShortCurrent index).contact.physicalState :=
  fun order => (run_contact_moment_control order index).1

theorem run_nextReceipt_moment_control (order index : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration (run stackedShortCurrent index).contact)) :
    Summable (momentDensity order ((run stackedShortCurrent index).nextReceipt.wholePath time)) ∧
      moment order ((run stackedShortCurrent index).nextReceipt.wholePath time) ≤
        runMomentBudget order (index + 1) := by
  have previous := run_contact_moment_control order index
  have actual := nextReceipt_moment_control (run stackedShortCurrent index) order previous.1 time
  refine ⟨actual.1, actual.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right previous.2 (Real.exp_pos _).le

theorem run_nextReceipt_momentRegular (index : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration (run stackedShortCurrent index).contact)) :
    MomentRegular ((run stackedShortCurrent index).nextReceipt.wholePath time) :=
  fun order => (run_nextReceipt_moment_control order index time).1

theorem run_receipt_moment_control (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    Summable (momentDensity order ((run stackedShortCurrent index).receipt.wholePath time)) ∧
      moment order ((run stackedShortCurrent index).receipt.wholePath time) ≤
        runMomentBudget order index := by
  cases index with
  | zero => exact stacked_short_receipt_all_moments order time
  | succ index => exact run_nextReceipt_moment_control order index time

theorem run_receipt_momentRegular (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    MomentRegular ((run stackedShortCurrent index).receipt.wholePath time) :=
  fun order => (run_receipt_moment_control order index time).1

end
end SaturationMonoid.NavierStokes.NativeFullOrderNext
