import H0mework.Fock.HistoryConditional.OperatorAcquisitionColumns

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationAcquisition

open SourceCopyProgram (Index)
open SourceCopyTimeModel (mass time)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def massRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Window runtime index →ₗ[ℂ] ℂ :=
  ((((index.val + 1 : Nat) : ℂ) ^ 2 - 1)⁻¹) •
    (columns runtime index steps (secondColumn runtime index nonunit steps) (Fin.last (index.val + 1)) -
      columns runtime index steps 0 0 - columns runtime index steps 0 (Fin.last (index.val + 1)))

theorem overlap_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) : (((index.val + 1 : Nat) : ℂ) ^ 2 - 1) ≠ 0 := by
  have positive : 1 < (index.val + 1) ^ 2 := by
    have large : 2 ≤ index.val + 1 := by omega
    nlinarith
  intro zero
  have same : (index.val + 1) ^ 2 = 1 := by exact_mod_cast (sub_eq_zero.mp zero)
  exact (ne_of_gt positive) same

theorem mass_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    massRead runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) value) = mass value := by
  simp only [massRead, LinearMap.smul_apply, LinearMap.sub_apply, columns_source, smul_eq_mul]
  change ((((index.val + 1 : Nat) : ℂ) ^ 2 - 1)⁻¹) *
    (inner ℂ (SourceColumnForcing.column (inventoryBound runtime) index 1) (time (index.val + 1) value) -
      inner ℂ (SourceColumnForcing.column (inventoryBound runtime) index 0) value -
      inner ℂ (SourceColumnForcing.column (inventoryBound runtime) index 0) (time (index.val + 1) value)) = _
  rw [overlap, inv_mul_cancel_left₀ (overlap_nonzero runtime index nonunit)]

def clockRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Window runtime index →ₗ[ℂ] ℂ :=
  (((index.val + 1 : Nat) : ℂ)⁻¹) •
    (columns runtime index steps 0 (Fin.last (index.val + 1)) - massRead runtime index nonunit steps) -
      ((index.val + 1 : Nat) : ℂ) • massRead runtime index nonunit steps

theorem clock_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    clockRead runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) value) = SourceJointClockGraph.clock value := by
  simp only [clockRead, LinearMap.sub_apply, LinearMap.smul_apply, mass_source, columns_source, smul_eq_mul]
  change (((index.val + 1 : Nat) : ℂ)⁻¹) *
    (inner ℂ (SourceColumnForcing.column (inventoryBound runtime) index 0) (time (index.val + 1) value) - mass value) -
      ((index.val + 1 : Nat) : ℂ) * mass value = _
  rw [first_tail, add_sub_cancel_left, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)), add_sub_cancel_right]

end
end SourceOperatorObservationAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
