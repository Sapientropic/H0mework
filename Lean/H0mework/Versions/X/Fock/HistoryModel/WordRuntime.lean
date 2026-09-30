import H0mework.Versions.X.Fock.HistoryModel.SourceWords

/-! The original new-actor Family consumer receives the computed action-word model at its literal next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

def nextValue (depth : Nat) : WholeModel (depth + 1) :=
  letterAction (depth + 1) (.inl ()) (point (depth + 1) (runtimeAt depth).current.visit.current)

theorem nextValue_is_source (depth : Nat) :
    nextValue depth = point (depth + 1) (runtimeAt depth).tick.next.current.visit.current := by
  exact (action_point (depth + 1) (.inl ()) ((runtimeAt depth).current.visit.current : Current)).trans
    (congrArg (point (depth + 1))
      ((runtimePayload depth).nativeWrite.target_eq.symm.trans (runtime_current_next depth).symm))

theorem nextValue_is_original_fibre (depth : Nat) :
    restrict (depth + 1) (nextValue depth) = (FamilyModel.Fock.realizedNext depth).val := by
  exact (congrArg (restrict (depth + 1)) (nextValue_is_source depth)).trans
    (restrict_point (depth + 1) ((runtimeAt depth).tick.next.current.visit.current : Current))

theorem native_word_information (depth : Nat) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    restrict (depth + 1) (nextValue depth) = (FamilyModel.Fock.realizedNext depth).val ∧
      FamilyModel.Fock.forgetLast depth (restrict (depth + 1) (nextValue depth)) =
        FamilyModel.Fock.action depth (FamilyModel.Fock.point depth runtime.current.visit.current) ∧
      (∀ word : List (Letter (depth + 1)), ∀ index : FamilyModel.Fock.Index (depth + 1),
        FamilyModel.Fock.readout (depth + 1)
          (restrict (depth + 1) (run (letterAction (depth + 1)) word (nextValue depth))) index =
          sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material (depth + 1) index)
            (actualWord (depth + 1) word stage.next.current.visit.current))) ∧
      FamilyModel.Fock.readout (depth + 1) (restrict (depth + 1) (nextValue depth))
          (FamilyModel.Fock.newestIndex depth) =
        sourceStateAt (NativeCopy.copy stage.next.current.visit.current stage.next.current.visit.current) ∧
      (∀ index : FamilyModel.Fock.Index depth,
        NativeCopy.Fock.material depth index = (runtimeAt index.val).current.visit.current ∧
          NativeCopy.Fock.material (depth + 1) (FamilyModel.Fock.oldIndex depth index) = NativeCopy.Fock.material depth index) ∧
      NativeCopy.Fock.material (depth + 1) (FamilyModel.Fock.newestIndex depth) = stage.next.current.visit.current ∧
      (runtimePayload depth).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, runtimePayload depth⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      (runtimeFacade.process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) ∧
      stage.next.current.visit.current = (runtimePayload depth).nativeWrite.target := by
  rcases FamilyModel.Fock.runtime_family_next_factorizes depth with
    ⟨_point, previous, _fibre, oldMaterials, newestMaterial, newestRead,
      occurrence, face, installation, stageFacts, nextCurrent⟩
  refine ⟨nextValue_is_original_fibre depth, ?_, ?_, ?_, oldMaterials, newestMaterial,
    occurrence, face, installation, stageFacts, nextCurrent⟩
  · rw [nextValue_is_original_fibre]
    exact previous
  · intro word index
    rw [nextValue_is_source]
    exact read_word (depth + 1) word _ index
  · rw [nextValue_is_original_fibre]
    exact newestRead

end
end SourceGeneratedActionWords.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
