import H0mework.Versions.X.Fock.HistoryConditional.NativeBirthSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Key : Type*} [DecidableEq Key]

def informationIncrement (count : Nat) : ℝ :=
  ((count + 1 : Nat) : ℝ) * Real.log (count + 1 : Nat) - (count : ℝ) * Real.log count

theorem count_log_next (read : Nat → Key) (bound : Nat) :
    (∑ actor : Fin (bound + 2),
      Real.log ((SourceConditionalNativeObservers.generate read (bound + 1) (read actor.val)).1 : ℝ)) =
    (∑ actor : Fin (bound + 1),
      Real.log ((SourceConditionalNativeObservers.generate read bound (read actor.val)).1 : ℝ)) +
        informationIncrement (SourceConditionalNativeObservers.generate read bound (read (bound + 1))).1 := by
  let count := (SourceConditionalNativeObservers.generate read bound (read (bound + 1))).1
  let change : ℝ := Real.log (count + 1 : Nat) - Real.log count
  have old (actor : Fin (bound + 1)) :
      Real.log ((SourceConditionalNativeObservers.generate read (bound + 1) (read actor.val)).1 : ℝ) =
        Real.log ((SourceConditionalNativeObservers.generate read bound (read actor.val)).1 : ℝ) +
          (if read actor.val = read (bound + 1) then change else 0) := by
    rw [SourceConditionalNativeObservers.generated_next]
    by_cases same : read actor.val = read (bound + 1)
    · simp only [SourceConditionalNativeObservers.advance, same, ite_true]
      dsimp only [change, count]
      ring
    · simp only [SourceConditionalNativeObservers.advance, if_neg same, add_zero]
  have bias : (∑ actor : Fin (bound + 1), if read actor.val = read (bound + 1) then change else 0) =
      (count : ℝ) * change := by
    have counted := congrArg (fun value : Nat => (value : ℝ))
      (SourceConditionalNativePosterior.count_sum read bound (read (bound + 1)))
    push_cast at counted
    change _ = ((SourceConditionalNativeObservers.generate read bound (read (bound + 1))).1 : ℝ) * change
    rw [counted, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro actor _
    split_ifs <;> simp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  simp_rw [old]
  rw [Finset.sum_add_distrib, bias, SourceConditionalNativeObservers.generated_next]
  simp only [SourceConditionalNativeObservers.advance]
  dsimp only [informationIncrement, change, count]
  push_cast
  ring

theorem information_next (runtime : LivingRuntimeState process) (read : Nat → Key) :
    ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) *
      SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime.tick.next))
        (fun actor : Actors runtime.tick.next => read actor.val)
        (SourceConditionalNext.Image.actual (nextRead runtime.tick.next)) (positive runtime.tick.next) =
    ((inventoryBound runtime + 1 : Nat) : ℝ) *
      SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
        (fun actor : Actors runtime => read actor.val)
        (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) +
      informationIncrement (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 := by
  rw [SourceConditionalInformationLoss.information_count, SourceConditionalInformationLoss.information_count,
    SourceConditionalInventory.sum_count, SourceConditionalInventory.sum_count]
  change (∑ actor : Fin (inventoryBound runtime.tick.next + 1),
    Real.log ((SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) (read actor.val)).1 : ℝ)) = _
  rw [SourceActualImageStep.next_bound, count_log_next]

variable {Coarse : Type*} [DecidableEq Coarse]

theorem amount_next (runtime : LivingRuntimeState process) (read : Nat → Key) (forget : Key → Coarse) :
    ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) * SourceConditionalInformationLoss.amount runtime.tick.next read forget =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalInformationLoss.amount runtime read forget +
        informationIncrement (SourceConditionalNativeMerge.count read forget (inventoryBound runtime)
          (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (forget (read (inventoryBound runtime + 1)))) -
        informationIncrement (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 := by
  rw [SourceConditionalNativeMerge.count_generated]
  have fine := information_next runtime read
  have coarse := information_next runtime (forget ∘ read)
  have current := congrArg (fun value : ℝ => ((inventoryBound runtime + 1 : Nat) : ℝ) * value)
    (SourceConditionalInformationLoss.information_balance runtime read forget)
  have next := congrArg (fun value : ℝ => ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) * value)
    (SourceConditionalInformationLoss.information_balance runtime.tick.next read forget)
  simp only [Function.comp_apply] at coarse
  simp only [mul_add] at current next
  linarith

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
