import H0mework.Probability.Empirical.ConditionalFormula
import H0mework.Probability.Empirical.Retained
import H0mework.Fock.SourceHistory.Installed

/-! The original native next consumes complete conditional transfer and retained source information. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalTransfer.Installed

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B)

def currentNext (depth : Nat) : Field (process := process) read :=
  fieldPoint (process := process) read (runtimeAt depth).tick.next.state

theorem currentNext_eq_atom (depth : Nat) :
    currentNext read depth = nextAtom read runtimeSeed depth (Fin.last depth) := by
  rw [nextAtom, fieldSample, fieldPoint_action]
  rfl

theorem currentNext_supported (depth : Nat) :
    currentNext read depth ∈ (fieldPMF read runtimeSeed.tick.next depth).support := by
  rw [nextPMF_from_indices]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨Fin.last depth, by simp [historyPMF], (currentNext_eq_atom read depth).symm⟩

theorem runtime_transfer_factorizes (depth : Nat) (value : Space read runtimeSeed depth) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    currentNext read depth = fieldPoint read stage.next.state ∧
      transfer read runtimeSeed depth value (currentNext read depth) =
        conditionalValue read runtimeSeed depth value (currentNext read depth) (currentNext_supported read depth) ∧
      (∀ index : Fin (depth + 1),
        (index ∈ (conditionalIndices read runtimeSeed depth (currentNext read depth)
          (currentNext_supported read depth)).support ↔ nextAtom read runtimeSeed depth index = currentNext read depth) ∧
        let actor := (history runtimeSeed depth).stageAt index
        nextAtom read runtimeSeed depth index = fieldPoint read actor.next.state ∧
          actor.next.current.visit.current = (runtimePayload index.val).nativeWrite.target ∧
          (process.toAnswerNextCausalWorld.emitted (ULift.up (sample runtimeSeed depth index)) =
              ULift.up actor.activated.generated ∧
            actor.activated.generated.occurrence =
              (runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
                (runtimeAt index.val).current.visit.current ∧
            HEq actor.wholeLedgerWriteBack
              ((runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
                (runtimeAt index.val).current.visit.current) ∧
            actor.next.current = actor.activated.nextCurrent)) ∧
      reconstruct read runtimeSeed depth (retainedUpdate read runtimeSeed depth value) = value ∧
      ‖value‖ ^ 2 = ‖transfer read runtimeSeed depth value‖ ^ 2 +
        ‖residual read runtimeSeed depth value‖ ^ 2 ∧
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
  refine ⟨rfl, transfer_at_atom read runtimeSeed depth value _ _, ?_,
    reconstruct_split read runtimeSeed depth value, energy_decomposition read runtimeSeed depth value,
    (runtimePayload depth).sourceOccurrence_eq, runtimeReadout_is_particleWave depth, installed.2.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes, runtime_current_next depth⟩
  intro index
  refine ⟨conditionalIndices_support_iff read runtimeSeed depth _ _ index, ?_,
    runtime_current_next index.val, sample_factorizes runtimeSeed depth index⟩
  exact fieldPoint_action read (sample runtimeSeed depth index)

end
end SourceConditionalTransfer.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
