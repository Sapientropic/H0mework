import H0mework.Versions.R2.Fock.Cofinal.LogicEvidence

/-! Dependent logical evidence is consumed by the original state and root factorization. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationLogic

open ParticleWaveFock ParticleWaveFockRuntime ParticleWaveFockOperationPrefix
open ParticleWaveFockOperationEnvelope ParticleWaveFockOperationCochain
open ParticleWaveFockOperationDerivation SourceOperationEffects SourceOperationInventoryLift
open SourceOperationLogic

noncomputable section

abbrev TargetReadEvidence (depth : Nat) (word : FormalCarrier) :=
  ∀ bound (index : Fin (bound + 1)),
    PLift (let seen := stageInventory ((materialHistory depth bound).stageAt index) word
      seen.1 + seen.2 = (payloadAt ((runtimeAt depth).advance index.val)).targetState)

/-- All representatives of the actual source point read the target; no representative is selected. -/
def everyRepresentativeReadsTarget (depth : Nat) :
    ForallEvidence (sourceMap depth) (TargetReadEvidence depth)
      (q (sourceMap depth) OperationRelations.operationWord) := by
  intro representative bound index
  have sameImage : sourceMap depth representative.val =
      sourceMap depth OperationRelations.operationWord := by
    have sourceEquality := (q_eq_iff (sourceMap depth) _ _).mp representative.property
    simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using sourceEquality
  have sameStage := (envelope_source_fibre_iff depth representative.val
    OperationRelations.operationWord).mp sameImage bound index
  refine ⟨?_⟩
  dsimp only
  rw [sameStage, stage_reads_installed_payload]
  have receipt := stage_state_from_derivation ((materialHistory depth bound).stageAt index)
  dsimp only at receipt
  rw [(stageDerivation ((materialHistory depth bound).stageAt index)).sound] at receipt
  exact receipt

def recoveredActualSource (depth : Nat) : Σ word : FormalCarrier, TermEvidence depth word :=
  existsEvidenceElim (sourceMap depth) (TermEvidence depth)
    ⟨q (sourceMap depth) OperationRelations.operationWord, actualWitness depth⟩

/-- Dependent elimination consumes the retained proof tree before the original state law. -/
theorem actualWitness_reads_state (depth bound : Nat) (index : Fin (bound + 1)) :
    let seen := (liftExpr (recoveredActualSource depth).2.1).eval
      (stageEnvironment ((materialHistory depth bound).stageAt index))
    seen.1 + seen.2 = (payloadAt ((runtimeAt depth).advance index.val)).targetState := by
  dsimp only
  have reading := ((recoveredActualSource depth).2.2.2 bound index).sound
  rw [reading]
  exact (stage_state_from_boundary ((materialHistory depth bound).stageAt index)).symm

theorem actualWitness_factorizes (depth bound : Nat) (index : Fin (bound + 1)) :
    let stage := (materialHistory depth bound).stageAt index
    let runtime := (runtimeAt depth).advance index.val
    let seen := (liftExpr (recoveredActualSource depth).2.1).eval (stageEnvironment stage)
    seen.1 + seen.2 = (payloadAt runtime).targetState ∧
    (runtimeFacade.readoutAt runtime .particleWave =
        .inl ⟨activeAt runtime, payloadAt runtime⟩ ∧
      stage.activated.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent) := by
  have source := stage_derivation_factorizes ((materialHistory depth bound).stageAt index)
  exact ⟨actualWitness_reads_state depth bound index, source.2⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationLogic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
