import H0mework.Versions.X.NavierStokes.SourceAction.FinitePrefixWindow
import H0mework.Versions.X.NavierStokes.SourceAction.ReceiptSpacetime
import H0mework.Physics.Holonomic.AnholonomicSource
import Mathlib.Analysis.SpecialFunctions.Sigmoid

set_option autoImplicit false
open scoped BigOperators Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeFinitePrefixTimeChart

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open PhysicsCore.ProofFreeRicherAnholonomicSource
open NativeFullOrderSynthesis NativeSpacetimeControl NativeReceiptTimeProfile NativeFullOrderTime
open NativeStressSource

noncomputable section

def duration (index : ℕ) : ℝ := WholePrefixState.duration stackedShortCurrent (index + 2)

theorem duration_pos (index : ℕ) : 0 < duration index := WholePrefixState.duration_pos _ _

def receipt (index : ℕ) := WholePrefixReceipt.receipt stackedShortCurrent (index + 2)
def window (index : ℕ) : Window (receipt index) := NativeFinitePrefixUnifiedWindow.window (index + 2)

def physicalTime (index : ℕ) (parameter : ℝ) : ℝ := duration index * Real.sigmoid parameter

theorem physicalTime_mem (index : ℕ) (parameter : ℝ) : physicalTime index parameter ∈ Ioo (0 : ℝ) (duration index) :=
  ⟨mul_pos (duration_pos index) (Real.sigmoid_pos parameter),
    (mul_lt_mul_of_pos_left (Real.sigmoid_lt_one parameter) (duration_pos index)).trans_eq (mul_one _)⟩

def timePoint (index : ℕ) (parameter : ℝ) : Ioo (0 : ℝ) (duration index) :=
  ⟨physicalTime index parameter, physicalTime_mem index parameter⟩

def inverseTime (index : ℕ) (actual : ℝ) : ℝ := -Real.log ((actual / duration index)⁻¹ - 1)

theorem physicalTime_inverse (index : ℕ) (actual : ℝ) (inside : actual ∈ Ioo (0 : ℝ) (duration index)) :
    physicalTime index (inverseTime index actual) = actual := by
  have ratioPositive : 0 < actual / duration index := div_pos inside.1 (duration_pos index)
  have ratioLt : actual / duration index < 1 := (div_lt_one (duration_pos index)).mpr inside.2
  have logPositive : 0 < (actual / duration index)⁻¹ - 1 := by
    rw [sub_pos, one_lt_inv_iff₀]
    exact ⟨ratioPositive, ratioLt⟩
  simp only [physicalTime, inverseTime, Real.sigmoid, neg_neg, Real.exp_log logPositive]
  rw [show 1 + ((actual / duration index)⁻¹ - 1) = (actual / duration index)⁻¹ by ring, inv_inv]
  exact mul_div_cancel₀ _ (duration_pos index).ne'

theorem physicalTime_injective (index : ℕ) : Function.Injective (physicalTime index) := by
  intro first second same
  exact Real.sigmoid_injective (mul_left_cancel₀ (duration_pos index).ne' same)

theorem inverseTime_physicalTime (index : ℕ) (parameter : ℝ) : inverseTime index (physicalTime index parameter) = parameter :=
  physicalTime_injective index (physicalTime_inverse index _ (physicalTime_mem index parameter))

def clockRate (index : ℕ) (parameter : ℝ) : ℝ :=
  duration index * (Real.sigmoid parameter * (1 - Real.sigmoid parameter))

theorem clockRate_pos (index : ℕ) (parameter : ℝ) : 0 < clockRate index parameter :=
  mul_pos (duration_pos index) (mul_pos (Real.sigmoid_pos parameter) (sub_pos.mpr (Real.sigmoid_lt_one parameter)))

theorem physicalTime_hasDerivAt (index : ℕ) (parameter : ℝ) :
    HasDerivAt (physicalTime index) (clockRate index parameter) parameter :=
  (Real.hasDerivAt_sigmoid parameter).const_mul (duration index)

theorem physicalTime_contDiff (index : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (physicalTime index) :=
  contDiff_const.mul (contDiff_sigmoid.of_le le_top)

def spatialRead (point : BasePoint) : PhysicalSpace := WithLp.toLp 2 (fun direction => point direction.succ)

def spacetime (index : ℕ) (point : BasePoint) : Spacetime := (physicalTime index (point 0), spatialRead point)

theorem spatialRead_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) spatialRead := by
  apply (contDiff_piLp 2).mpr
  intro direction
  exact contDiff_piLp_apply 2

theorem spacetime_contDiff (index : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (spacetime index) :=
  ((physicalTime_contDiff index).comp (contDiff_piLp_apply 2)).prodMk spatialRead_contDiff

theorem spacetime_mem (index : ℕ) (point : BasePoint) : spacetime index point ∈ NativeReceiptSpacetime.slab (window index) :=
  ⟨⟨(physicalTime_mem index (point 0)).1.le, (physicalTime_mem index (point 0)).2.le⟩, trivial⟩

def field (index : ℕ) (point : BasePoint) : PhysicalSpace := NativeReceiptSpacetime.field (receipt index) (spacetime index point)

theorem field_contDiff (index : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (field index) := by
  rw [← contDiffOn_univ]
  exact (NativeReceiptSpacetime.field_contDiffOn (window index)).comp (spacetime_contDiff index).contDiffOn
    (fun point _ => spacetime_mem index point)

def sourcePoint (index : ℕ) (actual : ℝ) (space : PhysicalSpace) : BasePoint :=
  WithLp.toLp 2 (Fin.cases (inverseTime index actual) (fun direction => space direction))

theorem sourcePoint_time (index : ℕ) (actual : ℝ) (space : PhysicalSpace) : sourcePoint index actual space 0 = inverseTime index actual := rfl

theorem spatialRead_sourcePoint (index : ℕ) (actual : ℝ) (space : PhysicalSpace) : spatialRead (sourcePoint index actual space) = space := by
  ext direction
  rfl

theorem field_original_read (index : ℕ) (actual : ℝ) (inside : actual ∈ Ioo (0 : ℝ) (duration index)) (space : PhysicalSpace) :
    field index (sourcePoint index actual space) =
      spatialField (wholeBiotSavartVelocityState ((receipt index).wholePath ⟨actual, inside.1.le, inside.2.le⟩)) space := by
  unfold field spacetime
  rw [sourcePoint_time, spatialRead_sourcePoint, physicalTime_inverse index actual inside]
  unfold NativeReceiptSpacetime.field NativeReceiptSpacetime.velocity
  rw [NativeReceiptSpacetime.state_on_interval (receipt index) ⟨actual, inside.1.le, inside.2.le⟩]

def contactTime (index : ℕ) : ℝ := elapsedTime stackedShortCurrent (index + 1)
def nextContactTime (index : ℕ) : ℝ := elapsedTime stackedShortCurrent (index + 2)

theorem contactTime_mem (index : ℕ) : contactTime index ∈ Ioo (0 : ℝ) (duration index) :=
  NativeFinitePrefixUnifiedWindow.contact_interior stackedShortCurrent (index + 2) index (by omega)

theorem nextContactTime_mem (index : ℕ) : nextContactTime index ∈ Ioo (0 : ℝ) (duration index) :=
  NativeFinitePrefixUnifiedWindow.contact_interior stackedShortCurrent (index + 2) (index + 1) (by omega)

theorem contact_state (index : ℕ) :
    (receipt index).wholePath ⟨contactTime index, (contactTime_mem index).1.le, (contactTime_mem index).2.le⟩ =
      (run stackedShortCurrent index).contact.physicalState := by
  have source := NativeFinitePrefixUnifiedWindow.contact_read index
  convert source using 1
  congr 1

theorem next_contact_state (index : ℕ) :
    (receipt index).wholePath ⟨nextContactTime index, (nextContactTime_mem index).1.le, (nextContactTime_mem index).2.le⟩ =
      (run stackedShortCurrent index).next.contact.physicalState := by
  have source := NativeFinitePrefixUnifiedWindow.next_receipt_chart index
    ⟨(run stackedShortCurrent index).nextContact.time.1, (run stackedShortCurrent index).nextContact.time_pos.le, le_rfl⟩
  convert source using 1
  · congr 1
  · rw [next_contact]
    rfl

theorem contact_read (index : ℕ) (space : PhysicalSpace) :
    field index (sourcePoint index (contactTime index) space) =
      spatialField (wholeBiotSavartVelocityState (run stackedShortCurrent index).contact.physicalState) space := by
  rw [field_original_read index _ (contactTime_mem index), contact_state]

theorem next_contact_read (index : ℕ) (space : PhysicalSpace) :
    field index (sourcePoint index (nextContactTime index) space) =
      spatialField (wholeBiotSavartVelocityState (run stackedShortCurrent index).next.contact.physicalState) space := by
  rw [field_original_read index _ (nextContactTime_mem index), next_contact_state]

def velocity (index : ℕ) (parameter : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.velocity (receipt index) (physicalTime index parameter)

def velocityRate (index : ℕ) (parameter : ℝ) : ComplexVorticityHilbertState :=
  clockRate index parameter • NativeReceiptSpacetime.timeJet (window index) 1 (physicalTime index parameter)

theorem velocity_hasDerivAt (index : ℕ) (parameter : ℝ) :
    HasDerivAt (velocity index) (velocityRate index parameter) parameter := by
  have interior := physicalTime_mem index parameter
  have inside : physicalTime index parameter ∈ Icc (window index).first (window index).last :=
    ⟨interior.1.le, interior.2.le⟩
  have source := NativeReceiptSpacetime.timeJet_evolves (window index) 0 (physicalTime index parameter) inside
  have original : HasDerivWithinAt (NativeReceiptSpacetime.velocity (receipt index))
      (NativeReceiptSpacetime.timeJet (window index) 1 (physicalTime index parameter))
      (Icc (window index).first (window index).last) (physicalTime index parameter) :=
    source.congr_of_mem (fun time member => (NativeReceiptSpacetime.timeJet_zero (window index) time member).symm) inside
  exact (original.hasDerivAt (Icc_mem_nhds interior.1 interior.2)).scomp parameter (physicalTime_hasDerivAt index parameter)

theorem velocityRate_original_action (index : ℕ) (parameter : ℝ) (wave : IntegerWavevector) :
    velocityRate index parameter wave = clockRate index parameter •
      receiptMomentumAction (receipt index) wave (physicalTime index parameter) := by
  change clockRate index parameter • NativeReceiptSpacetime.timeJet (window index) 1 (physicalTime index parameter) wave = _
  rw [NativeReceiptSpacetime.timeJet_one_row (window index) _
    ⟨(physicalTime_mem index parameter).1.le, (physicalTime_mem index parameter).2.le⟩]

end
end SaturationMonoid.NavierStokes.NativeFinitePrefixTimeChart
