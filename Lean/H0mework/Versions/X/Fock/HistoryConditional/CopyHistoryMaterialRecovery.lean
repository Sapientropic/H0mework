import H0mework.Fock.HistoryConditional.CopyHistoryDecode
import H0mework.Versions.X.Fock.HistoryConditional.CopyHistoryConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

theorem decoded_actor (bound : Nat) (actor : Fin (bound + 1)) :
    decodeRow bound (SourceConditionalNativeObservers.generate (read bound) bound (read bound actor.val)).2 = some actor := by
  rw [native_row, decodeRow, List.find?_eq_some_iff_getElem]
  refine ⟨by simp, actor.val, by simpa only [List.length_finRange] using actor.isLt, ?_, ?_⟩
  · simp only [List.getElem_finRange]
    rfl
  · intro other earlier
    have inside : other < (List.finRange (bound + 1)).length := by
      simpa only [List.length_finRange] using earlier.trans actor.isLt
    have different : (List.finRange (bound + 1))[other] ≠ actor := by
      intro same
      have values := congrArg Fin.val same
      simp only [List.getElem_finRange, Fin.val_cast] at values
      omega
    change (!( (if (List.finRange (bound + 1))[other] = actor then (1 : ℚ) else 0) != 0)) = true
    rw [if_neg different]
    rfl

theorem decoded_empty (bound : Nat) : decodeRow bound (fun _ => 0) = none := by
  simp [decodeRow]

noncomputable section

def recoverMaterial (bound : Nat) (row : Fin (bound + 1) → ℚ) :
    Option ((actor : Fin (bound + 1)) × SourceGeneratedRuntimeMaterialStageAt (runtimeSeed.advance actor.val)) :=
  (decodeRow bound row).map (fun actor => ⟨actor, (history runtimeSeed bound).stageAt actor⟩)

theorem recovered_material (bound : Nat) (actor : Fin (bound + 1)) :
    recoverMaterial bound (SourceConditionalNativeObservers.generate (read bound) bound (read bound actor.val)).2 =
      some ⟨actor, (history runtimeSeed bound).stageAt actor⟩ := by
  rw [recoverMaterial, decoded_actor]
  rfl

theorem recovered_factorizes (bound : Nat) (actor : Fin (bound + 1)) :
    type_of% (recovered_material bound actor) ∧ type_of% (sample_factorizes runtimeSeed bound actor) :=
  ⟨recovered_material bound actor, sample_factorizes runtimeSeed bound actor⟩

theorem decoded_effect (runtime : LivingRuntimeState process) (actor : SourceConditionalModel.Actors runtime) :
    (decodeRow (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)
      (SourceConditionalNativeObservers.generate (read (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
        (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)
        (read (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) actor.val)).2).map
        (fun recovered => SourceCopyNativeSharedUpdate.modelStep runtime.tick.next (SourceConditionalModel.nextRead runtime recovered)) =
      some (SourceConditionalNativePosterior.model runtime.tick.next
        (read (SourceGeneratedAcquisitionContinuation.inventoryBound runtime.tick.next))
        (read (SourceGeneratedAcquisitionContinuation.inventoryBound runtime.tick.next)
          (SourceActualImageStep.advanceIndex runtime actor).val)) := by
  rw [decoded_actor]
  simp only [Option.map_some]
  congr 1
  rw [model_recovers]
  exact SourceActualImageStep.model_step_source runtime actor

end
end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
