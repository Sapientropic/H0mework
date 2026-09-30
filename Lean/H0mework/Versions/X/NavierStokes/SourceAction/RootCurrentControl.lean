import H0mework.Versions.X.NavierStokes.SourceAction.CurrentReadout
import H0mework.Versions.X.NavierStokes.SourceAction.ChartPhysicalAction
import H0mework.Versions.X.NavierStokes.SourceAction.RootSourceAction
import H0mework.Versions.X.NavierStokes.SourceAction.PhysicalCurrent

set_option autoImplicit false
open scoped ContDiff Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRootCurrentConsumer

open Set Filter MeasureTheory
open PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderSynthesis NativeSourceCurrentReadout
open NativeSourceUnifiedActionSplice (target target_is_original_next)
open NativeFinitePrefixTimeChart (sourcePoint contactTime nextContactTime duration)

noncomputable section

/-- This read uses the further original compiler-generated prefix, without changing its earlier authority. -/
def physicalCurrent (index : ℕ) (direction : Fin 4) (time : ℝ) (space : PhysicalSpace) : ℝ :=
  current (matter index) (dual index) direction (sourcePoint index time space)

def momentum (index : ℕ) (time : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.timeJet (NativeFinitePrefixTimeChart.window index) 1 time

theorem field_physical_read (index : ℕ) (time : ℝ) (inside : time ∈ Ioo (0 : ℝ) (duration index))
    (space : PhysicalSpace) :
    NativeFinitePrefixTimeChart.field index (sourcePoint index time space) =
      spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) time) space := by
  rw [NativeFinitePrefixTimeChart.field_original_read index time inside]
  unfold NativeReceiptSpacetime.velocity
  rw [NativeReceiptSpacetime.state_on_interval (NativeFinitePrefixTimeChart.receipt index)
    ⟨time, inside.1.le, inside.2.le⟩]

theorem spatial_physical_read (index : ℕ) (time : ℝ) (inside : time ∈ Ioo (0 : ℝ) (duration index))
    (space : PhysicalSpace) (direction : Fin 3) :
    physicalCurrent index direction.succ time space =
      spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) time) space direction := by
  rw [physicalCurrent, spatial_read]
  exact congrArg (fun value : PhysicalSpace => value direction) (field_physical_read index time inside space)

theorem temporal_physical_read (index : ℕ) (time : ℝ) (inside : time ∈ Ioo (0 : ℝ) (duration index))
    (space : PhysicalSpace) : physicalCurrent index 0 time space =
      2 + ‖spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) time) space‖ ^ 2 / 8 := by
  rw [physicalCurrent, temporal_read, field_physical_read index time inside]

theorem target_initial_current (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    physicalCurrent index direction.succ (contactTime index) space =
      spatialField (wholeBiotSavartVelocityState (target index).initialState) space direction := by
  rw [physicalCurrent, NativeSourceCurrentReadout.contact_read, target_is_original_next]
  rfl

theorem target_contact_current (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    physicalCurrent index direction.succ (nextContactTime index) space =
      spatialField (wholeBiotSavartVelocityState (target index).contact.physicalState) space direction := by
  rw [physicalCurrent, NativeSourceCurrentReadout.next_contact_read, target_is_original_next]

theorem target_initial_field (index : ℕ) (space : PhysicalSpace) :
    spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) (contactTime index)) space =
      spatialField (wholeBiotSavartVelocityState (target index).initialState) space := by
  rw [← field_physical_read index _ (NativeFinitePrefixTimeChart.contactTime_mem index),
    NativeFinitePrefixTimeChart.contact_read, target_is_original_next]
  rfl

theorem target_contact_field (index : ℕ) (space : PhysicalSpace) :
    spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) (nextContactTime index)) space =
      spatialField (wholeBiotSavartVelocityState (target index).contact.physicalState) space := by
  rw [← field_physical_read index _ (NativeFinitePrefixTimeChart.nextContactTime_mem index),
    NativeFinitePrefixTimeChart.next_contact_read, target_is_original_next]

theorem target_initial_temporal_current (index : ℕ) (space : PhysicalSpace) :
    physicalCurrent index 0 (contactTime index) space =
      2 + ‖spatialField (wholeBiotSavartVelocityState (target index).initialState) space‖ ^ 2 / 8 := by
  rw [temporal_physical_read index _ (NativeFinitePrefixTimeChart.contactTime_mem index), target_initial_field]

theorem target_contact_temporal_current (index : ℕ) (space : PhysicalSpace) :
    physicalCurrent index 0 (nextContactTime index) space =
      2 + ‖spatialField (wholeBiotSavartVelocityState (target index).contact.physicalState) space‖ ^ 2 / 8 := by
  rw [temporal_physical_read index _ (NativeFinitePrefixTimeChart.nextContactTime_mem index), target_contact_field]

theorem spatial_current_hasDerivAt (index : ℕ) (time : ℝ)
    (inside : time ∈ Ioo (0 : ℝ) (duration index)) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun actual => physicalCurrent index direction.succ actual space)
      (spatialField (momentum index time) space direction) time := by
  have source := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivAt time
    (NativeTimeChartPhysicalAction.source_physical_clock_hasDerivAt index time inside space)
  apply source.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 inside.2] with actual member
  exact spatial_physical_read index actual member space direction

theorem temporal_current_hasDerivAt (index : ℕ) (time : ℝ)
    (inside : time ∈ Ioo (0 : ℝ) (duration index)) (space : PhysicalSpace) :
    HasDerivAt (fun actual => physicalCurrent index 0 actual space)
      (inner ℝ (spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) time) space)
        (spatialField (momentum index time) space) / 4) time := by
  have original := ((NativeTimeChartPhysicalAction.source_physical_clock_hasDerivAt index time inside space).norm_sq.div_const 8).const_add 2
  have source : HasDerivAt (fun actual => 2 +
      ‖spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) actual) space‖ ^ 2 / 8)
      (inner ℝ (spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) time) space)
        (spatialField (momentum index time) space) / 4) time := by
    convert! original using 1
    dsimp only [momentum]
    ring
  apply source.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 inside.2] with actual member
  exact temporal_physical_read index actual member space

theorem target_initial_momentum_row (index : ℕ) (wave : IntegerWavevector) :
    momentum index (contactTime index) wave = biotSavartVelocityCoefficient wave
      (classicalWholeNSVorticityTangent butterflyGainViscosity (target index).initialState wave) := by
  have original := NativeSourceUnifiedActionSplice.source_momentum_jet index wave
  rw [NativeSourceUnifiedActionSplice.contactTime_value] at original
  exact original

theorem target_contact_momentum_row (index : ℕ) (wave : IntegerWavevector) :
    momentum index (nextContactTime index) wave = biotSavartVelocityCoefficient wave
      (classicalWholeNSVorticityTangent butterflyGainViscosity (target index).contact.physicalState wave) := by
  rw [momentum, NativeReceiptSpacetime.timeJet_one_row (NativeFinitePrefixTimeChart.window index) _
    ⟨(NativeFinitePrefixTimeChart.nextContactTime_mem index).1.le, (NativeFinitePrefixTimeChart.nextContactTime_mem index).2.le⟩,
    NativeStressSource.receiptMomentumAction]
  change biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff
    (NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) (nextContactTime index)) wave) = _
  rw [NativeReceiptSpacetime.state_on_interval (NativeFinitePrefixTimeChart.receipt index)
    ⟨nextContactTime index, (NativeFinitePrefixTimeChart.nextContactTime_mem index).1.le,
      (NativeFinitePrefixTimeChart.nextContactTime_mem index).2.le⟩,
    NativeFinitePrefixTimeChart.next_contact_state, target_is_original_next]
  rfl

theorem target_initial_current_hasDerivAt (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun actual => physicalCurrent index direction.succ actual space)
      (spatialField (momentum index (contactTime index)) space direction) (contactTime index) :=
  spatial_current_hasDerivAt index _ (NativeFinitePrefixTimeChart.contactTime_mem index) space direction

theorem target_contact_current_hasDerivAt (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun actual => physicalCurrent index direction.succ actual space)
      (spatialField (momentum index (nextContactTime index)) space direction) (nextContactTime index) :=
  spatial_current_hasDerivAt index _ (NativeFinitePrefixTimeChart.nextContactTime_mem index) space direction

theorem target_initial_temporal_hasDerivAt (index : ℕ) (space : PhysicalSpace) :
    HasDerivAt (fun actual => physicalCurrent index 0 actual space)
      (inner ℝ (spatialField (wholeBiotSavartVelocityState (target index).initialState) space)
        (spatialField (momentum index (contactTime index)) space) / 4) (contactTime index) := by
  simpa only [target_initial_field] using temporal_current_hasDerivAt index _ (NativeFinitePrefixTimeChart.contactTime_mem index) space

theorem target_contact_temporal_hasDerivAt (index : ℕ) (space : PhysicalSpace) :
    HasDerivAt (fun actual => physicalCurrent index 0 actual space)
      (inner ℝ (spatialField (wholeBiotSavartVelocityState (target index).contact.physicalState) space)
        (spatialField (momentum index (nextContactTime index)) space) / 4) (nextContactTime index) := by
  simpa only [target_contact_field] using temporal_current_hasDerivAt index _ (NativeFinitePrefixTimeChart.nextContactTime_mem index) space

theorem root_current_all_order_Lp (index order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain)
    (contained : domain ⊆ NativeCurrentPhysicalReadout.physicalDomain index) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDeriv ℝ order (fun point : BasePoint =>
        physicalCurrent index direction (point 0) (NativeFinitePrefixTimeChart.spatialRead point)))
          exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (fun point : BasePoint =>
        physicalCurrent index direction (point 0) (NativeFinitePrefixTimeChart.spatialRead point)))
          exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  NativeCurrentPhysicalReadout.physical_all_order_Lp index order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeRootCurrentConsumer
