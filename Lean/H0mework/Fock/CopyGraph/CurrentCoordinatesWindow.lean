import H0mework.Fock.CopyGraph.CurrentCoordinatesColumn

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time mass)
open SourceCopyRecordedRecurrence (cutoff windowBound priorIndex)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

abbrev Window (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :=
  PrefixCarrier SourceJointClockGraph.Carrier (windowBound runtime index steps)

def response (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (phase : Fin (windowBound runtime index steps + 1)) : Window runtime index steps →ₗ[ℂ] ℂ :=
  (((innerSL ℂ (SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps))).comp
    (SourceCopyGraph.action (inventoryBound runtime) index)).toLinearMap).comp (LinearMap.proj phase)

theorem response_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (phase : Fin (windowBound runtime index steps + 1)) (target : SourceJointClockGraph.Carrier) :
    response runtime index steps phase (recordedPrefix runtime index steps (windowBound runtime index steps) target) =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps), time phase.val target⟫_ℂ := by
  change ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps),
    SourceCopyGraph.action (inventoryBound runtime) index
      (recordedPrefix runtime index steps (windowBound runtime index steps) target phase)⟫_ℂ = _
  rw [SourceCopyTemporalBoundary.prefix_source, observed_column]

def massRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Window runtime index steps →ₗ[ℂ] ℂ :=
  (((cutoff runtime index steps + 1 : Nat) : ℂ)⁻¹) •
    (response runtime index steps (Fin.last (windowBound runtime index steps)) -
      response runtime index steps (priorIndex runtime index steps))

theorem mass_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    massRead runtime index steps
        (recordedPrefix runtime index steps (windowBound runtime index steps) target) = mass target := by
  simp only [massRead, LinearMap.smul_apply, LinearMap.sub_apply, response_source, smul_eq_mul]
  change (((cutoff runtime index steps + 1 : Nat) : ℂ)⁻¹) *
    (⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps),
      time (cutoff runtime index steps + 2) target⟫_ℂ -
      ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps),
        time (cutoff runtime index steps + 1) target⟫_ℂ) = _
  rw [tail_difference]
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _) :
    ((cutoff runtime index steps + 1 : Nat) : ℂ) ≠ 0) _

def clockRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Window runtime index steps →ₗ[ℂ] ℂ :=
  (((cutoff runtime index steps + 1 : Nat) : ℂ)⁻¹) •
    (response runtime index steps (priorIndex runtime index steps) - massRead runtime index steps) -
      ((cutoff runtime index steps + 1 : Nat) : ℂ) • massRead runtime index steps

theorem clock_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    clockRead runtime index steps
        (recordedPrefix runtime index steps (windowBound runtime index steps) target) = SourceJointClockGraph.clock target := by
  simp only [clockRead, LinearMap.sub_apply, LinearMap.smul_apply, mass_source, response_source, smul_eq_mul]
  change (((cutoff runtime index steps + 1 : Nat) : ℂ)⁻¹) *
    (⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps),
      time (cutoff runtime index steps + 1) target⟫_ℂ - mass target) -
      ((cutoff runtime index steps + 1 : Nat) : ℂ) * mass target = _
  rw [tail_pairing _ _ _ _ (by omega)]
  have nonzero : ((cutoff runtime index steps + 1 : Nat) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  field_simp
  ring

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
