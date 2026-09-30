import H0mework.NavierStokes.SourceAction.FinitePrefixWindow
import H0mework.NavierStokes.SourceAction.ReceiptSpacetime
import H0mework.NavierStokes.Accumulation.NativeFluidMediumRoot
import H0mework.Foundation.Authority.Representation

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeSourceUnifiedActionSplice

open Set Filter
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeReceiptTimeProfile NativeReceiptSpacetime NativeSpacetimeControl NativeFullOrderTime
open NativeFinitePrefixUnifiedWindow

noncomputable section

def occurrenceRead (index : ℕ)
    (occurrence : (nativeTemporalSource stackedShortCurrent).toRootSource.actual.OccurrenceAt (.finite index)) :
    GeneratedWholeRestartNativeActualOccurrenceAt stackedShortCurrent index :=
  match occurrence with
  | ⟨_, .finite _ actual⟩ => actual

def visit (index : ℕ) : SourceNativeTemporalVisitAt (nativeTemporalRoot stackedShortCurrent) where
  current := .finite index
  history := .finite (by
    have source := ((nativeTemporalProductiveHistory stackedShortCurrent).visitAt index).history
    simpa only [ProductiveFiniteRootHistoryAt.visitAt_current, nativeTemporalProductiveHistory] using source)

def authority (index : ℕ) := (nativeTemporalAuthoritativeRoot stackedShortCurrent).authoritativeEvolutionAt (visit index)

def actual (index : ℕ) := occurrenceRead index (authority index).toLedgerReadout.occurrence

def target (index : ℕ) : GeneratedWholeRestartCurrent butterflyGainViscosity := (actual index).response.1

theorem root_projection_is_original (index : ℕ) :
    HEq ((authority index).toLedgerReadout.projectionOutcome
        (world := nativeTemporalAuthoritativeRoot stackedShortCurrent) PUnit.unit)
      ((nativeTemporalAuthoritativeRoot stackedShortCurrent).projectionOutcomeAt PUnit.unit (.finite index)) :=
  (authority index).toLedgerReadout.projectionOutcome_heq_sourceOutcome PUnit.unit

theorem actual_is_original (index : ℕ) :
    actual index = generatedWholeRestartNativeActualOccurrence stackedShortCurrent index := by
  unfold actual
  rw [(authority index).toLedgerReadout.occurrence_eq]
  rfl

theorem target_is_original_next (index : ℕ) : target index = (run stackedShortCurrent index).next := by
  rw [target, actual_is_original]
  rfl

def receipt (index : ℕ) := WholePrefixReceipt.receipt stackedShortCurrent (index + 2)
/-- A further finite compiler-generated extension through `index + 2`, not a future payload
already installed in `authority index`. Earlier contact/next reads below are restrictions into it. -/
def controlled (index : ℕ) : Window (receipt index) := window (index + 2)

def contactTime (index : ℕ) : Icc (0 : ℝ) (WholePrefixState.duration stackedShortCurrent (index + 2)) :=
  chartTime stackedShortCurrent (index + 2) index (by omega)
    ⟨(run stackedShortCurrent index).contact.time.1, (run stackedShortCurrent index).contact.time_pos.le, le_rfl⟩

theorem contactTime_value (index : ℕ) : (contactTime index).1 = elapsedTime stackedShortCurrent (index + 1) := by
  simp only [contactTime, chartTime, elapsedTime_succ]

theorem contactTime_interior (index : ℕ) :
    (contactTime index).1 ∈ Ioo (controlled index).first (controlled index).last := by
  rw [contactTime_value]
  exact contact_interior stackedShortCurrent (index + 2) index (by omega)

/-- The target is read from the complete original root occurrence before it is identified in the controlled carrier. -/
theorem source_target_read (index : ℕ) :
    state (receipt index) (contactTime index).1 = (target index).initialState := by
  rw [state_on_interval (receipt index) (contactTime index), target_is_original_next]
  exact contact_read index

theorem source_next_receipt_read (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).nextContact.time.1) :
    (receipt index).wholePath (chartTime stackedShortCurrent (index + 2) (index + 1) (by omega) time) =
      state (target index).receipt time.1 := by
  rw [target_is_original_next]
  exact (next_receipt_chart index time).trans (state_on_interval (run stackedShortCurrent index).nextReceipt
    ⟨time.1, time.2.1, time.2.2.trans (run stackedShortCurrent index).nextContact.time.2.2⟩).symm

theorem source_momentum_jet (index : ℕ) (wave : IntegerWavevector) :
    timeJet (controlled index) 1 (contactTime index).1 wave =
      biotSavartVelocityCoefficient wave
        (classicalWholeNSVorticityTangent butterflyGainViscosity (target index).initialState wave) := by
  have inside := contactTime_interior index
  rw [timeJet_one_row (controlled index) _ ⟨inside.1.le, inside.2.le⟩,
    NativeStressSource.receiptMomentumAction]
  change biotSavartVelocityCoefficient wave
    (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff
      (state (receipt index) (contactTime index).1) wave) = _
  rw [source_target_read]
  rfl

theorem source_velocity_hasDerivAt (index : ℕ) :
    HasDerivAt (velocity (receipt index)) (timeJet (controlled index) 1 (contactTime index).1)
      (contactTime index).1 := by
  have interior := contactTime_interior index
  have inside : (contactTime index).1 ∈ Icc (controlled index).first (controlled index).last :=
    ⟨interior.1.le, interior.2.le⟩
  have source := timeJet_evolves (controlled index) 0 (contactTime index).1 inside
  have actual : HasDerivWithinAt (velocity (receipt index))
      (timeJet (controlled index) 1 (contactTime index).1)
      (Icc (controlled index).first (controlled index).last) (contactTime index).1 :=
    source.congr_of_mem (fun time member => (timeJet_zero (controlled index) time member).symm) inside
  exact actual.hasDerivAt (Icc_mem_nhds interior.1 interior.2)

theorem source_momentum_hasDerivAt (index : ℕ) (wave : IntegerWavevector) :
    HasDerivAt (fun time => velocity (receipt index) time wave)
      (biotSavartVelocityCoefficient wave
        (classicalWholeNSVorticityTangent butterflyGainViscosity (target index).initialState wave))
      (contactTime index).1 := by
  have source := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt
    (contactTime index).1 (source_velocity_hasDerivAt index)
  change HasDerivAt (fun time => velocity (receipt index) time wave)
    (timeJet (controlled index) 1 (contactTime index).1 wave) (contactTime index).1 at source
  rw [source_momentum_jet] at source
  exact source

theorem source_spacetime_control (index : ℕ) (modes : Finset IntegerWavevector) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field (receipt index)) (slab (controlled index)) ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField (receipt index)) (slab (controlled index)) ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField (receipt index) modes) (slab (controlled index)) :=
  ⟨field_contDiffOn (controlled index), vorticityField_contDiffOn (controlled index),
    correctionField_contDiffOn (controlled index) modes⟩

end
end SaturationMonoid.NavierStokes.NativeSourceUnifiedActionSplice
