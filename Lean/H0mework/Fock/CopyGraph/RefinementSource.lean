import H0mework.Fock.CopyGraph.DecoderSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceCopyProgram (Index)
noncomputable section
universe u v
variable {Fine : Type u} [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
variable {Coarse : Type v} [MeasurableSpace Coarse]

def lift (bound : Nat) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse) :
    Space (observed (historyPMF bound) (forget ∘ fine)) →L[ℂ] Space (observed (historyPMF bound) fine) :=
  (transfer (historyPMF bound) fine).comp (pullback (historyPMF bound) (forget ∘ fine)).toContinuousLinearMap

theorem decoder_source (bound : Nat) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : Space (observed (historyPMF bound) (forget ∘ fine))) :
    pullback (historyPMF bound) fine (decoderValue (historyPMF bound) fine (fun atom => value (forget atom))) =
      pullback (historyPMF bound) (forget ∘ fine) value := by
  apply MeasureTheory.Lp.ext
  apply Filter.Eventually.of_forall
  intro actor
  rw [pullback_at _ _ _ actor (source_positive bound actor),
    decoderValue_at _ _ _ (fine actor) (observed_supported _ _ actor (source_positive bound actor)),
    pullback_at _ _ _ actor (source_positive bound actor)]
  rfl

theorem lift_source (bound : Nat) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : Space (observed (historyPMF bound) (forget ∘ fine))) :
    pullback (historyPMF bound) fine (lift bound fine forget value) = pullback (historyPMF bound) (forget ∘ fine) value := by
  change pullback (historyPMF bound) fine
    (transfer (historyPMF bound) fine (pullback (historyPMF bound) (forget ∘ fine) value)) = _
  rw [← decoder_source, IsometricRetainedTransfer.transfer_pullback]

theorem lift_norm (bound : Nat) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : Space (observed (historyPMF bound) (forget ∘ fine))) : ‖lift bound fine forget value‖ = ‖value‖ := by
  rw [← (pullback (historyPMF bound) fine).norm_map, lift_source,
    (pullback (historyPMF bound) (forget ∘ fine)).norm_map]

theorem action_lift (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : Space (observed (historyPMF bound) (forget ∘ fine))) :
    SourceConditionalGraphDecoder.action depth bound index fine (lift bound fine forget value) =
      SourceConditionalGraphDecoder.action depth bound index (forget ∘ fine) value := by
  rw [SourceConditionalGraphDecoder.action_source, SourceConditionalGraphDecoder.action_source, lift_source]

theorem image_inclusion (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse) :
    (SourceConditionalGraphDecoder.action depth bound index (forget ∘ fine)).range ≤
      (SourceConditionalGraphDecoder.action depth bound index fine).range := by
  rintro value ⟨source, rfl⟩
  exact ⟨lift bound fine forget source, action_lift depth bound index fine forget source⟩

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
