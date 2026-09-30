import H0mework.Versions.X.Fock.HistoryModel.Counted.Word
import H0mework.Versions.X.Fock.HistoryConditional.GWordConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordDynamicNext

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation SourceConditionalModel
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- The original source-law weights follow every actual word, with the original actor as index. -/
theorem source_word_law (bound : Nat)
    (word : List (SourceGeneratedActionWords.Fock.Letter (bound + 1))) :
    (((SourceGeneratedActionWords.Fock.sourceLaw bound).map nativeStep).map
      (SourceGeneratedActionWords.Fock.actualWord (bound + 1) word)).map
        (SourceGeneratedActionWords.Fock.point (bound + 1)) =
      (historyPMF bound).map (fun actor : Fin (bound + 1) =>
        SourceGeneratedActionWords.run
          (SourceGeneratedActionWords.Fock.letterAction (bound + 1)) word
          (SourceGeneratedActionWords.Fock.point (bound + 1)
            (((history runtimeSeed bound).stageAt actor).next.current.visit.current : Current))) := by
  let nextState : Fin (bound + 1) → Current := fun actor =>
    (((history runtimeSeed bound).stageAt actor).next.current.visit.current : Current)
  have law := congrArg (fun p : PMF Current =>
      (p.map (SourceGeneratedActionWords.Fock.actualWord (bound + 1) word)).map
        (SourceGeneratedActionWords.Fock.point (bound + 1)))
      (SourceGeneratedActionWords.Fock.nativeLaw_next bound)
  have first := PMF.map_comp nextState (historyPMF bound)
    (SourceGeneratedActionWords.Fock.actualWord (bound + 1) word)
  have second := PMF.map_comp
    (fun actor : Fin (bound + 1) =>
      SourceGeneratedActionWords.Fock.actualWord (bound + 1) word (nextState actor))
    (historyPMF bound) (SourceGeneratedActionWords.Fock.point (bound + 1))
  calc
    _ = ((historyPMF bound).map nextState |>.map
        (SourceGeneratedActionWords.Fock.actualWord (bound + 1) word)).map
          (SourceGeneratedActionWords.Fock.point (bound + 1)) := law
    _ = (historyPMF bound).map (fun actor =>
        SourceGeneratedActionWords.Fock.point (bound + 1)
          (SourceGeneratedActionWords.Fock.actualWord (bound + 1) word (nextState actor))) := by
      rw [first]
      simpa only [Function.comp_def] using second
    _ = _ := by
      congr 1
      funext actor
      exact (SourceGeneratedActionWords.Fock.word_point (bound + 1) word (nextState actor)).symm

/-- Both original model and GWord act on the same source-generated executed index. -/
theorem actor_word_model (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    SourceGeneratedActionWords.run
      (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
        (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current)) =
    SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
      ((finiteVisit (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
        (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state))).current) := by
  change SourceGeneratedActionWords.run
      (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
        (finiteVisit (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state)).current) = _
  exact SourceCopyNativeWord.model_effect (inventoryBound runtime + 1) word
    (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state)

theorem actor_word_g (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor =
      SourceJointClockGraph.read (SourceClockComplex.ofNative
        (SourceOperationNative.statePoint process
          (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
            (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state)))) := by
  rw [SourceCompiledGWord.image, SourceOperationNative.point]
  rw [SourceCompiledWordOperator.action_original,
    SourceCompiledWordOperator.word_point]

/-- The old unit reader and the physical G point see the same executed source index. -/
theorem actor_word_task_square (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    let depth := inventoryBound runtime + 1
    let executed := SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
      (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state)
    (SourceOwnedObservationHistory.FamilyModel.Fock.readout depth
      (SourceGeneratedActionWords.Fock.restrict depth
        (SourceGeneratedActionWords.run (SourceGeneratedActionWords.Fock.letterAction depth) word
          (SourceGeneratedActionWords.Fock.point depth
            (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current)))) 0,
      SourceCompiledGWord.image runtime depth word actor) =
    (sourceStateAt (finiteVisit executed).current,
      SourceJointClockGraph.read (SourceClockComplex.ofNative
        (SourceOperationNative.statePoint process executed))) := by
  dsimp only
  apply Prod.ext
  · have model := congrArg (fun value : SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) =>
        SourceOwnedObservationHistory.FamilyModel.Fock.readout (inventoryBound runtime + 1)
          (SourceGeneratedActionWords.Fock.restrict (inventoryBound runtime + 1) value) 0)
      (actor_word_model runtime word actor)
    let executed := SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
      (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state)
    have restricted := congrArg
      (fun value : SourceOwnedObservationHistory.FamilyModel.Fock.WholeModel (inventoryBound runtime + 1) =>
        SourceOwnedObservationHistory.FamilyModel.Fock.readout (inventoryBound runtime + 1) value 0)
      (SourceGeneratedActionWords.Fock.restrict_point (inventoryBound runtime + 1)
        (finiteVisit executed).current)
    exact model.trans (restricted.trans
      ((SourceOwnedObservationHistory.FamilyModel.Fock.point_read (inventoryBound runtime + 1)
        (finiteVisit executed).current 0).trans
        (SourceGeneratedActionWords.Fock.Dynamic.Hilbert.unit_reader_sourceState
          (inventoryBound runtime + 1) (finiteVisit executed).current)))
  · exact actor_word_g runtime word actor

private theorem point_runtime_injective (depth : Nat) : Function.Injective
    (fun state : Nat => SourceGeneratedActionWords.Fock.point depth
      ((runtimeAt state).current.visit.current : Current)) := by
  intro left right same
  have mapped := congrArg
    (SourceGeneratedActionWords.completionEquiv
      (SourceGeneratedActionWords.Fock.actions depth)
      (SourceGeneratedActionWords.Fock.observer depth) (.inl ())) same
  have complete : SourceGeneratedActionWords.Fock.Complete.point depth
      ((runtimeAt left).current.visit.current : Current) =
      SourceGeneratedActionWords.Fock.Complete.point depth
        ((runtimeAt right).current.visit.current : Current) := by
    simpa only [SourceGeneratedActionWords.Fock.point,
      SourceGeneratedActionWords.Fock.Complete.point,
      SourceGeneratedActionWords.completion_equiv_source] using mapped
  exact SourceGeneratedActionWords.Fock.Dynamic.Hilbert.point_runtime_injective depth complete

theorem actor_word_injective (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1))) :
    Function.Injective (fun actor : Actors runtime =>
      SourceGeneratedActionWords.run
        (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
        (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
          (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current))) := by
  intro left right same
  have sameOutput := (actor_word_model runtime word left).symm.trans
    (same.trans (actor_word_model runtime word right))
  have samePoint : SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
      ((runtimeAt (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
        (((history runtimeSeed (inventoryBound runtime)).stageAt left).next.state))).current.visit.current : Current) =
      SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
      ((runtimeAt (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
        (((history runtimeSeed (inventoryBound runtime)).stageAt right).next.state))).current.visit.current : Current) := by
    simpa only [runtimeAt_current, finiteVisit_current] using sameOutput
  have sameIndex := point_runtime_injective (inventoryBound runtime + 1) samePoint
  have sameState :
      (((history runtimeSeed (inventoryBound runtime)).stageAt left).next.state) =
      (((history runtimeSeed (inventoryBound runtime)).stageAt right).next.state) := by
    apply SourceCompiledWordOperator.index_injective (word.map SourceCopyNativeWord.encode)
    simpa only [SourceCopyWordAffine.execute_original] using sameIndex
  have sameActor : left.val = right.val := by
    change (runtimeAt left.val).tick.next.state = (runtimeAt right.val).tick.next.state at sameState
    change (runtimeAt left.val).state + 1 = (runtimeAt right.val).state + 1 at sameState
    rw [runtimeAt_state, runtimeAt_state] at sameState
    exact Nat.add_right_cancel sameState
  exact Fin.ext sameActor

theorem source_word_mass (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    ((((SourceGeneratedActionWords.Fock.sourceLaw (inventoryBound runtime)).map nativeStep).map
      (SourceGeneratedActionWords.Fock.actualWord (inventoryBound runtime + 1) word)).map
        (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)))
          (SourceGeneratedActionWords.run
            (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
            (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
              (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current))) =
      historyPMF (inventoryBound runtime) actor := by
  let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
    fun index => SourceGeneratedActionWords.run
      (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
        (((history runtimeSeed (inventoryBound runtime)).stageAt index).next.current.visit.current : Current))
  have faithful : Function.Injective read := actor_word_injective runtime word
  rw [source_word_law]
  rw [PMF.map_apply, tsum_eq_single actor]
  · exact if_pos rfl
  · intro candidate different
    exact if_neg (fun same => different (faithful same).symm)

theorem source_word_actor_posterior (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
      fun index => SourceGeneratedActionWords.run
        (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
        (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
          (((history runtimeSeed (inventoryBound runtime)).stageAt index).next.current.visit.current : Current))
    SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) read (read actor)
      (SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) read actor
        (positive runtime actor)) = PMF.pure actor := by
  dsimp only
  let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
    fun index => SourceGeneratedActionWords.run
      (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
        (((history runtimeSeed (inventoryBound runtime)).stageAt index).next.current.visit.current : Current))
  exact SourceWeightedRecovery.ObservationRefinement.conditional_injective
    (historyPMF (inventoryBound runtime)) read (actor_word_injective runtime word) actor
    (positive runtime actor)

theorem source_word_g_recovers (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
      fun index => SourceGeneratedActionWords.run
        (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
        (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
          (((history runtimeSeed (inventoryBound runtime)).stageAt index).next.current.visit.current : Current))
    (∑ candidate : Actors runtime,
      (((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) read (read actor)
        (SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) read actor
          (positive runtime actor))) candidate).toReal : ℂ) •
        SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word candidate) =
      SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor := by
  dsimp only
  rw [source_word_actor_posterior runtime word actor]
  rw [Finset.sum_eq_single actor]
  · simp
  · intro candidate _ different
    rw [PMF.pure_apply, if_neg different]
    simp
  · intro absent
    exact (absent (Finset.mem_univ actor)).elim

end
end SourceWordDynamicNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
