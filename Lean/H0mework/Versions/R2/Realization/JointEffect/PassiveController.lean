import H0mework.Versions.R2.Realization.JointEffect.FoldResidual

/-!
# Root controller for a passive dependent joint effect

A dependent face need not fake local dynamical progress when the root compiler
already generated the temporal successor.  This controller totally disposes
the complete source/target pairing inventories as a passive carry, a precise
history/tree/joint residual, or the compiler terminal.  The installed raw
face, whole ledger and next remain one canonical root image.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open CofinalHistoryTransition
open RootedAccountedUnfoldingZip
open RootLawDependentJointStateController
open RootLawDependentJointTransition

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

structure GeneratedPassiveCarryAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    Type (u + 1) where
  historyTransition : GeneratedStepJointTransitionAt step successor
  pairingAlignment : RootedAccountedUnfoldingZip.GeneratedZipAt
    (stepSourcePairingOccurrence step)
    (stepTargetPairingOccurrence step successor)
  generatedTree : RootedAccountedUnfolding
    (GeneratedNodeAt step successor historyTransition.history)
  tree_exact : settleTree step successor historyTransition.history
      (alignedJointOccurrence step successor historyTransition.history
        pairingAlignment) = .inl generatedTree
  generated_rooted : generatedTree.map GeneratedNodeAt.pair =
    (alignedJointOccurrence step successor historyTransition.history
      pairingAlignment).map Sigma.fst

def generatePassiveCarry
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (transition : GeneratedStepJointTransitionAt step successor)
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step)
      (stepTargetPairingOccurrence step successor))
    (generatedTree : RootedAccountedUnfolding
      (GeneratedNodeAt step successor transition.history))
    (tree_exact : settleTree step successor transition.history
      (alignedJointOccurrence step successor transition.history alignment) =
        .inl generatedTree) : GeneratedPassiveCarryAt step successor where
  historyTransition := transition
  pairingAlignment := alignment
  generatedTree := generatedTree
  tree_exact := tree_exact
  generated_rooted := settleTree_generated_projects step successor
    transition.history _ generatedTree tree_exact

theorem GeneratedPassiveCarryAt.source_tree_rooted
    {step : StepAt recognition visit} {successor : StepLedgerSuccessorAt step}
    (carry : GeneratedPassiveCarryAt step successor) :
    carry.generatedTree.map (fun node => node.pair.1) =
      stepSourcePairingOccurrence step := by
  rw [show (fun node : GeneratedNodeAt step successor
      carry.historyTransition.history => node.pair.1) =
      Prod.fst ∘ GeneratedNodeAt.pair by rfl]
  rw [← RootedAccountedUnfolding.map_map]
  rw [carry.generated_rooted]
  rw [RootedAccountedUnfolding.map_map]
  exact alignedJointOccurrence_source_rooted step successor
    carry.historyTransition.history carry.pairingAlignment

theorem GeneratedPassiveCarryAt.target_tree_rooted
    {step : StepAt recognition visit} {successor : StepLedgerSuccessorAt step}
    (carry : GeneratedPassiveCarryAt step successor) :
    carry.generatedTree.map (fun node => node.pair.2) =
      stepTargetPairingOccurrence step successor := by
  rw [show (fun node : GeneratedNodeAt step successor
      carry.historyTransition.history => node.pair.2) =
      Prod.snd ∘ GeneratedNodeAt.pair by rfl]
  rw [← RootedAccountedUnfolding.map_map]
  rw [carry.generated_rooted]
  rw [RootedAccountedUnfolding.map_map]
  exact alignedJointOccurrence_target_rooted step successor
    carry.historyTransition.history carry.pairingAlignment

theorem targetOccurrence_eq_emitted_of_commutes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    (emitted : (current : V.Current) →
      source.toRootSource.actual.OccurrenceAt current)
    (commutes : generated.CommutesWith emitted) :
    successor.targetOccurrence = emitted successor.targetCurrent := by
  cases generated with
  | nativeWrite => exact commutes
  | relationWrite => exact commutes
  | continuedTransport => exact commutes
  | borromeanRedirect => exact commutes
  | faithfulTerminal => exact nomatch successor

theorem successor_targetOccurrence_eq_emitted
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    successor.targetOccurrence = root.emitted successor.targetCurrent :=
  targetOccurrence_eq_emitted_of_commutes successor
    root.toAuthoritativeRoot.toLedgerRoot.emitted
    (root.toAuthoritativeRoot.toLedgerRoot.compiler_commutes visit.current)

theorem GeneratedPassiveCarryAt.target_installed_factorizes
    {step : StepAt recognition visit} {successor : StepLedgerSuccessorAt step}
    (_carry : GeneratedPassiveCarryAt step successor) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed (.inr PUnit.unit))
        successor.targetOccurrence)
      (recognition.material.toProjectionLaw.outcomeAt
        (.inr PUnit.unit) successor.targetOccurrence) :=
  recognition.installation.outcome_heq successor.targetOccurrence
    (.inr PUnit.unit)

inductive PassiveEffectDispositionAt
    (step : StepAt recognition visit) : Type (u + 1)
  | terminal (exact : stepSuccessor? step = none)
  | generatorResidual (successor : StepLedgerSuccessorAt step)
      (exact : stepSuccessor? step = some successor)
      (coordinate : GeneratorResidual (StepSourceHistory step)
        (StepTargetHistory step successor))
  | relationResidual (successor : StepLedgerSuccessorAt step)
      (exact : stepSuccessor? step = some successor)
      (generatorCompatible : (StepSourceHistory step).generatorClosure ≤
        (StepTargetHistory step successor).generatorClosure)
      (coordinate : RelationResidual (StepSourceHistory step)
        (StepTargetHistory step successor) generatorCompatible)
  | pairingShapeResidual (successor : StepLedgerSuccessorAt step)
      (exact : stepSuccessor? step = some successor)
      (transition : GeneratedStepJointTransitionAt step successor)
      (coordinate : RootedAccountedUnfoldingZip.ShapeResidualAt
        (stepSourcePairingOccurrence step)
        (stepTargetPairingOccurrence step successor))
  | allGenerated (successor : StepLedgerSuccessorAt step)
      (exact : stepSuccessor? step = some successor)
      (carry : GeneratedPassiveCarryAt step successor)
  | jointResidual (successor : StepLedgerSuccessorAt step)
      (exact : stepSuccessor? step = some successor)
      (transition : GeneratedStepJointTransitionAt step successor)
      (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
        (stepSourcePairingOccurrence step)
        (stepTargetPairingOccurrence step successor))
      (coordinate : ExactResidualAt step successor transition.history)
      (tree_exact : settleTree step successor transition.history
        (alignedJointOccurrence step successor transition.history alignment) =
          .inr coordinate)
      (coordinate_mem : ExactResidualAt.payload coordinate ∈
        (alignedJointOccurrence step successor transition.history
          alignment).trace)

noncomputable def settlePassiveEffect
    (step : StepAt recognition visit) : PassiveEffectDispositionAt step :=
  match exact : stepSuccessor? step with
  | none => .terminal exact
  | some successor =>
      match settleStepSuccessor step successor with
      | .generatorResidual coordinate =>
          .generatorResidual successor exact coordinate
      | .relationResidual compatible coordinate =>
          .relationResidual successor exact compatible coordinate
      | .generated transition =>
          match settlePairingAlignment step successor with
          | .shapeResidual coordinate =>
              .pairingShapeResidual successor exact transition coordinate
          | .generated alignment =>
              match tree_exact : settleTree step successor transition.history
                  (alignedJointOccurrence step successor transition.history
                    alignment) with
              | .inl generatedTree =>
                  .allGenerated successor exact
                    (generatePassiveCarry step successor transition alignment
                      generatedTree tree_exact)
              | .inr coordinate =>
                  .jointResidual successor exact transition alignment coordinate
                    tree_exact (settleTree_residual_mem_trace step successor
                      transition.history _ coordinate tree_exact)

theorem controllerMouth (step : StepAt recognition visit) :
    Nonempty (PassiveEffectDispositionAt step) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨⟨settlePassiveEffect step⟩,
    step.wholeLedgerWriteBack_eq_root, step.nextCurrent_eq_root⟩

theorem installedAuthority_factorizes (step : StepAt recognition visit) :
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    Nonempty (PassiveEffectDispositionAt step) ∧
      evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          (recognition.installation.embed (.inr PUnit.unit)))
        (recognition.material.toProjectionLaw.outcomeAt
          (.inr PUnit.unit) (root.emitted visit.current)) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  have factorization :=
    (root.canonicalCausalAnswerAndNext
      (ULift.up visit)).installedSubsystemAuthority_factorizes
        recognition.installation (.inr PUnit.unit)
  exact ⟨⟨settlePassiveEffect step⟩,
    factorization.1, factorization.2.1,
    step.wholeLedgerWriteBack_eq_root, factorization.2.2⟩

end


end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
