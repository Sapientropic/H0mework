import H0mework.Fock.RetainedCoarsening.Realization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

theorem coefficient_merge (bound stride : Nat) (frame : SourceRetainedReceiver.Frame Fine bound stride)
    (forget : Fine → Coarse) (coarse : Coarse) (actor : Fin (bound + 1)) :
    ((merge bound stride frame forget).native coarse).2 actor =
      ∑ key ∈ frame.keys, weight bound stride frame forget coarse key * (frame.native key).2 actor := by
  dsimp only [merge, SourceConditionalNativeMerge.inventoryMerge]
  apply Finset.sum_congr rfl
  intro key _
  by_cases selected : forget key = coarse <;> simp only [weight, selected, ↓reduceIte, zero_mul]

theorem model_merge (runtime : LivingRuntimeState process) (frame : SourceRetainedReceiver.At runtime Fine)
    (forget : Fine → Coarse) (coarse : Coarse) :
    SourceRetainedReceiver.model runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse =
      ∑ key ∈ frame.keys,
        (weight (inventoryBound runtime) (maximumIndex runtime).val frame forget coarse key : ℂ) •
          SourceRetainedReceiver.model runtime frame key := by
  simp only [SourceRetainedReceiver.model, coefficient_merge, Rat.cast_sum, Rat.cast_mul,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem residual_merge (runtime : LivingRuntimeState process) (frame : SourceRetainedReceiver.At runtime Fine)
    (forget : Fine → Coarse) (coarse : Coarse) :
    SourceRetainedReceiver.residual runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse =
      ∑ key ∈ frame.keys,
        (weight (inventoryBound runtime) (maximumIndex runtime).val frame forget coarse key : ℂ) •
          SourceRetainedReceiver.residual runtime frame key := by
  simp only [SourceRetainedReceiver.residual, value_merge, model_merge, map_sum, map_smul,
    Finset.sum_sub_distrib, smul_sub]

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
