import H0mework.Versions.X.Fock.HistoryModel.Next

/-! The installed native write owns the whole observer-inventory extension and its realized next fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FamilyModel.Fock

open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem runtime_family_next_factorizes (depth : Nat) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    (realizedNext depth).val = point (depth + 1) stage.next.current.visit.current ∧
      forgetLast depth (realizedNext depth).val = action depth (point depth runtime.current.visit.current) ∧
      (∀ candidate : WholeModel (depth + 1),
        forgetLast depth candidate = action depth (point depth runtime.current.visit.current) ↔
          candidate - (realizedNext depth).val ∈ LinearMap.ker (forgetLast depth)) ∧
      (∀ index : Index depth,
        NativeCopy.Fock.material depth index = (runtimeAt index.val).current.visit.current ∧
          NativeCopy.Fock.material (depth + 1) (oldIndex depth index) = NativeCopy.Fock.material depth index) ∧
      NativeCopy.Fock.material (depth + 1) (newestIndex depth) = stage.next.current.visit.current ∧
      readout (depth + 1) (realizedNext depth).val (newestIndex depth) =
        sourceStateAt (NativeCopy.copy stage.next.current.visit.current stage.next.current.visit.current) ∧
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
  have installed := coversAt_factorizes (runtimeAt depth) .particleWave
  have last : NativeCopy.Fock.material (depth + 1) (newestIndex depth) =
      (runtimeAt depth).tick.next.current.visit.current :=
    (newest_material depth).trans (runtime_current_next depth).symm
  have newest := (newest_readout depth).trans
    (congrArg (fun target => sourceStateAt (NativeCopy.copy target target)) (runtime_current_next depth).symm)
  exact ⟨rfl, (realizedNext depth).property, next_fibre_iff depth,
    (fun index => ⟨(window_actor_factorizes depth index).1, rfl⟩), last, newest,
    (runtimePayload depth).sourceOccurrence_eq, runtimeReadout_is_particleWave depth, installed.2.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes, runtime_current_next depth⟩

end
end SourceOwnedObservationHistory.FamilyModel.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
