import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionColumns

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index indexAfter scale)
open SourceCopyTimeModel (hilbert mass)
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory.SourceShift (basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem cotest_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (actor : Nat) (value : SourceJointClockGraph.Carrier) :
    ⟪cotest runtime index actor, value⟫_ℂ = hilbert value actor + mass value +
      (((index.val + 1 : Nat) : ℂ) ^ 2 * ((actor + 1 : Nat) : ℂ)) * SourceJointClockGraph.clock value := by
  rw [cotest, ContinuousLinearMap.adjoint_inner_left, SourceCopyCurrentCoordinates.column_pairing]
  change SourceCopyGraph.hilbertAction (inventoryBound runtime) index (hilbert value)
    (indexAfter (inventoryBound runtime) index actor) + mass value +
    ((indexAfter (inventoryBound runtime) index actor + 1 : Nat) : ℂ) *
      ((scale (inventoryBound runtime) index : ℂ) * SourceJointClockGraph.clock value) = _
  rw [SourceCopyTimeModel.action_coordinate, SourceCopyProgram.index_exact, SourceCopyProgram.scale_source]
  push_cast
  ring

theorem cotest_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (actor : Nat) :
    cotest runtime index actor = WithLp.toLp 2 (WithLp.toLp 2 (basis actor, (1 : ℂ)),
      (((index.val + 1 : Nat) : ℂ) ^ 2 * ((actor + 1 : Nat) : ℂ))) := by
  apply ext_inner_right ℂ
  intro value
  rw [cotest_pairing, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change hilbert value actor + mass value +
    (((index.val + 1 : Nat) : ℂ) ^ 2 * ((actor + 1 : Nat) : ℂ)) * SourceJointClockGraph.clock value =
    (⟪basis actor, hilbert value⟫_ℂ + ⟪(1 : ℂ), mass value⟫_ℂ) +
    ⟪(((index.val + 1 : Nat) : ℂ) ^ 2 * ((actor + 1 : Nat) : ℂ)), SourceJointClockGraph.clock value⟫_ℂ
  simp only [basis, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, map_mul, map_pow, map_natCast]
  ring

theorem cotest_gram (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (left right : Nat) :
    ⟪cotest runtime index left, cotest runtime index right⟫_ℂ =
      (if left = right then 1 else 0) + 1 +
        (((index.val + 1 : Nat) : ℂ) ^ 4 * ((left + 1 : Nat) : ℂ) * ((right + 1 : Nat) : ℂ)) := by
  rw [cotest_pairing, cotest_source]
  change basis right left + 1 +
    (((index.val + 1 : Nat) : ℂ) ^ 2 * ((left + 1 : Nat) : ℂ)) *
      (((index.val + 1 : Nat) : ℂ) ^ 2 * ((right + 1 : Nat) : ℂ)) = _
  by_cases same : left = right
  · subst right
    simp [basis, lp.single_apply]
    ring
  · simp [basis, lp.single_apply, same]
    ring

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
