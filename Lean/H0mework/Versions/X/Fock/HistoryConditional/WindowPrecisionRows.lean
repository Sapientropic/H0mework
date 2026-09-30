import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionCoefficients

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index indexAfter)
open SourceOperatorObservationAcquisition (secondColumn)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTimeModel (phaseAt)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def massCoefficients (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Coefficients runtime index steps :=
  ((((index.val + 1 : Nat) : ℂ) ^ 2 - 1)⁻¹) •
    (columnCoefficients runtime index steps (secondColumn runtime index nonunit steps) (Fin.last (index.val + 1)) -
      columnCoefficients runtime index steps 0 0 - columnCoefficients runtime index steps 0 (Fin.last (index.val + 1)))

theorem mass_original (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    evaluate runtime index steps (massCoefficients runtime index nonunit steps) =
      SourceOperatorObservationAcquisition.massRead runtime index nonunit steps := by
  rw [massCoefficients, map_smul, map_sub, map_sub, evaluate_column, evaluate_column, evaluate_column]
  rfl

def clockCoefficients (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Coefficients runtime index steps :=
  (((index.val + 1 : Nat) : ℂ)⁻¹) •
    (columnCoefficients runtime index steps 0 (Fin.last (index.val + 1)) - massCoefficients runtime index nonunit steps) -
      ((index.val + 1 : Nat) : ℂ) • massCoefficients runtime index nonunit steps

theorem clock_original (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    evaluate runtime index steps (clockCoefficients runtime index nonunit steps) =
      SourceOperatorObservationAcquisition.clockRead runtime index nonunit steps := by
  rw [clockCoefficients, map_sub, map_smul, map_sub, map_smul, evaluate_column, mass_original]
  rfl

def hilbertCoefficients (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (coordinate : Fin (cutoff runtime index steps + 1)) : Coefficients runtime index steps :=
  let actor := SourceCopySharedNext.columnAt runtime index steps coordinate
  let phase := phaseAt (inventoryBound runtime) index coordinate.val
  columnCoefficients runtime index steps actor phase.castSucc - massCoefficients runtime index nonunit steps -
    ((indexAfter (inventoryBound runtime) index actor.val + 1 : Nat) : ℂ) •
      (clockCoefficients runtime index nonunit steps + (phase.val : ℂ) • massCoefficients runtime index nonunit steps)

theorem hilbert_original (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (coordinate : Fin (cutoff runtime index steps + 1)) :
    evaluate runtime index steps (hilbertCoefficients runtime index nonunit steps coordinate) =
      SourceOperatorObservationAcquisition.hilbertRead runtime index nonunit steps coordinate := by
  simp only [hilbertCoefficients, map_sub, map_smul, map_add, evaluate_column, mass_original, clock_original]
  rfl

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
