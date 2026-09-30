import H0mework.NavierStokes.RecoveryAction.RecoveryWindow
import H0mework.NavierStokes.SourceAction.Mixed

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryMixedWindow

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open NativeFullOrderAction NativeFullOrderFlux NativeFullOrderSynthesis NativeFullOrderTime
open NativeRecoveryRowAction NativeRecoveryStrongWindow

noncomputable section

theorem hasDerivWithinAt_tsum_on_interval {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (left right : ℝ) (ordered : left < right) (field next : ι → ℝ → E) (fieldBound nextBound : ι → ℝ)
    (fieldPaid : Summable fieldBound) (nextPaid : Summable nextBound)
    (fieldContinuous : ∀ index, ContinuousOn (field index) (Icc left right))
    (nextContinuous : ∀ index, ContinuousOn (next index) (Icc left right))
    (evolves : ∀ index time, time ∈ Icc left right →
      HasDerivWithinAt (field index) (next index time) (Icc left right) time)
    (fieldBounded : ∀ index time, time ∈ Icc left right → ‖field index time‖ ≤ fieldBound index)
    (nextBounded : ∀ index time, time ∈ Icc left right → ‖next index time‖ ≤ nextBound index)
    (time : ℝ) (inside : time ∈ Icc left right) :
    HasDerivWithinAt (fun actual => ∑' index, field index actual) (∑' index, next index time) (Icc left right) time := by
  let shifted (curve : ℝ → E) (actual : ℝ) := curve (projIcc left right ordered.le (left + actual)).1
  have continuousShift (curve : ℝ → E) (continuous : ContinuousOn curve (Icc left right)) : Continuous (shifted curve) :=
    (continuous.domRestrict.comp continuous_projIcc).comp (continuous_const.add continuous_id)
  have maps : MapsTo (fun actual : ℝ => left + actual) (Icc (0 : ℝ) (right - left)) (Icc left right) := by
    intro actual member
    constructor <;> linarith [member.1, member.2]
  have same (curve : ℝ → E) (actual : ℝ) (member : actual ∈ Icc (0 : ℝ) (right - left)) :
      shifted curve actual = curve (left + actual) := by
    simp only [shifted, projIcc_of_mem ordered.le (maps member)]
  have point : time - left ∈ Icc (0 : ℝ) (right - left) := by
    constructor <;> linarith [inside.1, inside.2]
  have base := NativeMixedTimeSpace.hasDerivWithinAt_tsum_Icc_of_within (right - left) (sub_pos.mpr ordered)
    (fun index => shifted (field index)) (fun index => shifted (next index)) fieldBound nextBound fieldPaid nextPaid
    (fun index => continuousShift _ (fieldContinuous index)) (fun index => continuousShift _ (nextContinuous index))
    (fun index sample member => by
      have shift : HasDerivWithinAt (fun actual : ℝ => left + actual) 1 (Icc (0 : ℝ) (right - left)) sample := by
        simpa using ((hasDerivAt_id sample).const_add left).hasDerivWithinAt
      have actual := (evolves index (left + sample) (maps member)).scomp sample shift maps
      simp only [one_smul] at actual
      rw [same (next index) sample member]
      exact actual.congr_of_mem (fun sample member => same (field index) sample member) member)
    (fun index sample member => by rw [same (field index) sample member]; exact fieldBounded index _ (maps member))
    (fun index sample member => by rw [same (next index) sample member]; exact nextBounded index _ (maps member))
    ⟨time - left, point⟩
  have rateSame : (∑' index, shifted (next index) (time - left)) = ∑' index, next index time := by
    apply tsum_congr
    intro index
    rw [same (next index) (time - left) point, add_sub_cancel]
  rw [rateSame] at base
  have unshift : HasDerivWithinAt (fun actual : ℝ => actual - left) 1 (Icc left right) time := by
    simpa using ((hasDerivAt_id time).sub_const left).hasDerivWithinAt
  have returns : MapsTo (fun actual : ℝ => actual - left) (Icc left right) (Icc (0 : ℝ) (right - left)) := by
    intro actual member
    constructor <;> linarith [member.1, member.2]
  have actual := base.scomp time unshift returns
  simp only [one_smul] at actual
  apply actual.congr_of_mem _ inside
  intro sample member
  change (∑' index, field index sample) = ∑' index, shifted (field index) (sample - left)
  apply tsum_congr
  intro index
  rw [same (field index) (sample - left) (returns member), add_sub_cancel]

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {lower upper : ℝ}

def spatialWord (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  iteratedFDeriv ℝ order (spatialField (velocity receipt actual)) point directions

def physicalRateWord (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  iteratedFDeriv ℝ order (spatialField (rate receipt actual)) point directions

theorem spatialWord_eq_sum (window : ControlledWindow receipt lower upper)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    spatialWord receipt order directions point time =
      ∑' wave, observeWord order directions wave point (velocity receipt time wave) := by
  have moments (order : ℕ) : Summable fun wave => frequencySize wave ^ order * amplitude (velocity receipt time) wave :=
    summable_moment_of_square _ order (window.square_moments (order + 2) time inside).1
  rw [spatialWord, spatialField_word_eq _ moments]
  exact tsum_congr fun _ => rfl

theorem physicalRateWord_eq_sum (window : ControlledWindow receipt lower upper)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    physicalRateWord receipt order directions point time =
      ∑' wave, observeWord order directions wave point (rateRow receipt wave time) := by
  have moments (order : ℕ) : Summable fun wave => frequencySize wave ^ order * amplitude (rate receipt time) wave := by
    apply summable_moment_of_square
    have paid := (window.rate_moment_control (order + 2) time inside).1
    unfold velocityMomentDensity at paid
    simpa only [← pow_mul, Nat.mul_comm (order + 2) 2, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  rw [physicalRateWord, spatialField_word_eq _ moments]
  apply tsum_congr
  intro wave
  change observeWord order directions wave point (rate receipt time wave) = _
  rw [window.rate_row time inside wave]

theorem spatialWord_hasDerivWithinAt (window : ControlledWindow receipt lower upper)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    HasDerivWithinAt (spatialWord receipt order directions point)
      (physicalRateWord receipt order directions point time) (Icc window.first window.last) time := by
  have source := hasDerivWithinAt_tsum_on_interval window.first window.last window.ordered
    (fun wave actual => observeWord order directions wave point (velocity receipt actual wave))
    (fun wave actual => observeWord order directions wave point (rateRow receipt wave actual))
    (fun wave => (wordNorm order directions * Real.sqrt (window.budget (order + 4))) * decay wave)
    (fun wave => (wordNorm order directions * window.rateBudget order) * decay wave)
    (decay_summable.mul_left _) (decay_summable.mul_left _)
    (fun wave => ((observeWord order directions wave point).continuous.comp
      (velocity_row_continuous receipt wave)).continuousOn)
    (fun wave => (observeWord order directions wave point).continuous.comp_continuousOn
      (rateRow_continuousOn receipt _ window.velocity_continuous wave))
    (fun wave actual member => (observeWord order directions wave point).hasFDerivAt.comp_hasDerivWithinAt actual
      (window.row_hasDerivWithinAt wave actual member))
    (fun wave actual member => (observeWord_norm_le order directions wave point _).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (window.velocity_decay order actual member wave)
        (wordNorm_nonneg order directions)))
    (fun wave actual member => (observeWord_norm_le order directions wave point _).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (window.rate_decay order actual member wave)
        (wordNorm_nonneg order directions))) time inside
  rw [← physicalRateWord_eq_sum window order directions point time inside] at source
  exact source.congr_of_mem (fun actual member => spatialWord_eq_sum window order directions point actual member) inside

theorem source_spatialWord_hasDerivWithinAt (initial : GeneratedWholeRestartCurrent nu)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace)
    (time : ℝ) (inside : time ∈ Icc (sourceWindow initial).first (sourceWindow initial).last) :
    HasDerivWithinAt (spatialWord (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) order directions point)
      (physicalRateWord (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) order directions point time)
      (Icc (sourceWindow initial).first (sourceWindow initial).last) time :=
  spatialWord_hasDerivWithinAt (sourceWindow initial) order directions point time inside

def absoluteSpatialWord (initial : GeneratedWholeRestartCurrent nu)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  spatialWord (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) order directions point
    (actual - wholeRestartVelocityAccumulationTime initial)

theorem absoluteSpatialWord_eq_source (initial : GeneratedWholeRestartCurrent nu)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace)
    (time : Icc (wholeRestartVelocityAccumulationTime initial) (wholeRestartVelocityAccumulationTime initial + 1)) :
    absoluteSpatialWord initial order directions point time.1 =
      iteratedFDeriv ℝ order (spatialField (sourceGeneratedNativeTemporalAbsoluteWholePath initial time)) point directions := by
  exact congrArg (fun field : ComplexVorticityHilbertState => iteratedFDeriv ℝ order (spatialField field) point directions)
    (velocity_on_interval (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (endpointAbsoluteToLocalTime (wholeRestartVelocityAccumulationTime initial) time))

theorem absoluteSpatialWord_hasDerivWithinAt (initial : GeneratedWholeRestartCurrent nu)
    (order : ℕ) (directions : Fin order → PhysicalSpace) (point : PhysicalSpace)
    (time : ℝ)
    (inside : time ∈ Icc
      (wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).first)
      (wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).last)) :
    HasDerivWithinAt (absoluteSpatialWord initial order directions point)
      (physicalRateWord (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) order directions point
        (time - wholeRestartVelocityAccumulationTime initial))
      (Icc (wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).first)
        (wholeRestartVelocityAccumulationTime initial + (sourceWindow initial).last)) time := by
  let accumulation := wholeRestartVelocityAccumulationTime initial
  have localInside : time - accumulation ∈ Icc (sourceWindow initial).first (sourceWindow initial).last := by
    constructor <;> linarith [inside.1, inside.2]
  have original := source_spatialWord_hasDerivWithinAt initial order directions point (time - accumulation) localInside
  have shift : HasDerivWithinAt (fun actual : ℝ => actual - accumulation) 1
      (Icc (accumulation + (sourceWindow initial).first) (accumulation + (sourceWindow initial).last)) time := by
    simpa using ((hasDerivAt_id time).sub_const accumulation).hasDerivWithinAt
  have maps : MapsTo (fun actual : ℝ => actual - accumulation)
      (Icc (accumulation + (sourceWindow initial).first) (accumulation + (sourceWindow initial).last))
      (Icc (sourceWindow initial).first (sourceWindow initial).last) := by
    intro actual member
    constructor <;> linarith [member.1, member.2]
  have actual := original.scomp time shift maps
  simp only [one_smul] at actual
  convert! actual using 1

end
end SaturationMonoid.NavierStokes.NativeRecoveryMixedWindow
