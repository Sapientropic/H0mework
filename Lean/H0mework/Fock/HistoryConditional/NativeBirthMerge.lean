import H0mework.Fock.HistoryConditional.NativeBirthInnovation
import H0mework.Fock.HistoryConditional.NativeBirthInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem total_gap (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    total runtime (forget ∘ read) = total runtime read +
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalMergeLoss.gap runtime read forget := by
  have paid := congrArg (fun value : ℝ => ((inventoryBound runtime + 1 : Nat) : ℝ) * value)
    (SourceConditionalMergeLoss.loss runtime read forget)
  simp only [mul_add, SourceConditionalInventory.sum_count, ← SourceConditionalInventory.values_original,
    SourceConditionalMergeLoss.decoder_original] at paid
  rw [SourceConditionalMergeLoss.gap, SourceConditionalInventory.sum_count]
  simp only [SourceConditionalMergeLoss.decoder_original]
  simpa only [total, Function.comp_apply] using paid

theorem gap_next (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) * SourceConditionalMergeLoss.gap runtime.tick.next read forget =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalMergeLoss.gap runtime read forget +
        innovation runtime (forget ∘ read) - innovation runtime read := by
  have current := total_gap runtime read forget
  have next := total_gap runtime.tick.next read forget
  rw [minimum_update, minimum_update] at next
  linarith

omit [DecidableEq Coarse] in
def stalePenalty (runtime : LivingRuntimeState process) (read : Nat → Fine) : ℝ :=
  ‖SourceConditionalInventory.born (inventoryBound runtime) -
    SourceConditionalNativePosterior.decoder runtime read (read (inventoryBound runtime + 1))‖ ^ 2 /
      ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 + 1)

omit [DecidableEq Coarse] in
theorem stale_loss (runtime : LivingRuntimeState process) (read : Nat → Fine) :
    (∑ actor : Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        SourceConditionalNativePosterior.decoder runtime read (read actor.val)‖ ^ 2) =
      total runtime.tick.next read + stalePenalty runtime read := by
  rw [total_append]
  change total runtime read + _ = _
  rw [minimum_update, innovation, stalePenalty]
  have nonzero : ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 : ℝ) + 1 ≠ 0 := by
    positivity
  field_simp
  ring

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
