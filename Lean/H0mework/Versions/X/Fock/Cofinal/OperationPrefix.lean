import H0mework.Versions.X.Fock.Cofinal.SourceProjection
import H0mework.Realization.Operations.RuntimePrefix
import H0mework.Realization.ScalarCofinal.KernelCompletion
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Cofinal operation observations from sealed material history

Every finite evaluator is generated from the fixed Fock runtime's material stages.
Restriction retains the same earlier stages, so compatibility is produced directly.
The existing scalar completion reads every source/effect pair and retains the full
semantic fibre. This is a derived cofinal field, not a future table in a current atom.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

open SourceOperationEffects SourceOperationRelations
open ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedScalarCofinalKernelCompletion
open CategoryTheory
open ArithmeticGeneration

noncomputable section

abbrev FormalCarrier := SourceOperationRuntime.FormalCarrier ℤ OperationValue OperationVar OperationSort.parent
abbrev PrefixCarrier (stage : Nat) :=
  SourceOperationRuntime.PrefixCarrier OperationValue OperationSort.parent stage

def materialHistory (depth stage : Nat) :=
  SourceOperationRuntime.materialHistory (runtimeAt depth) stage

def oldEnvironment {runtime : LivingRuntimeState runtimeFacade.process}
    (_stage : SourceGeneratedRuntimeMaterialStageAt runtime) : Env OperationValue OperationVar :=
  fieldEnvironment (sourceFieldAt runtime.current.visit.current)

def incrementEnvironment {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) : Env OperationValue OperationVar :=
  fieldEnvironment (sourceFieldAt stage.next.current.visit.current -
    sourceFieldAt runtime.current.visit.current)

def stageInventory {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    FormalCarrier →ₗ[ℤ] ParentCarrier × ParentCarrier :=
  SourceOperationRuntime.stageInventory (R := ℤ) (s := OperationSort.parent)
    sourceMaterial environmentProjection stage

def activeAt (runtime : LivingRuntimeState runtimeFacade.process) :
    projectionLaw.ActiveAt PUnit.unit runtime.emittedOccurrence :=
  ⟨by
    change 1 ≤ scanIndex (finiteVisit runtime.state).current
    rw [finiteVisit_current]
    simp only [scanIndex, UnitHistory.cardinalShadow_generate]
    omega⟩

def payloadAt (runtime : LivingRuntimeState runtimeFacade.process) :
    RootGeneratedParticleWaveCurrentAt runtime.current.visit.current
      runtime.emittedOccurrence (activeAt runtime).down :=
  projectionLaw.project PUnit.unit runtime.emittedOccurrence (activeAt runtime)

theorem payload_is_readout (runtime : LivingRuntimeState runtimeFacade.process) :
    runtimeFacade.readoutAt runtime .particleWave =
      .inl ⟨activeAt runtime, payloadAt runtime⟩ := by
  change projectionLaw.outcomeAt PUnit.unit runtime.emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifierEq : projectionLaw.classify PUnit.unit runtime.emittedOccurrence = classification
  cases classification with
  | inl active =>
      have activeEq : active = activeAt runtime := by
        apply PLift.down_injective
        exact Subsingleton.elim _ _
      cases activeEq
      rfl
  | inr inactive =>
      have positive := (activeAt runtime).down
      have zero := inactive.down
      omega

theorem material_next_is_native_target
    {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    stage.next.current.visit.current =
      (payloadAt runtime).nativeWrite.target := by
  rw [(payloadAt runtime).nativeWrite_eq]
  rfl

theorem stage_reads_installed_payload
    {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    stageInventory stage OperationRelations.operationWord =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) := by
  rw [(payloadAt runtime).sourceState_eq, (payloadAt runtime).forcedTrace_eq]
  change
    (evaluation (s := OperationSort.parent) (oldEnvironment stage) OperationRelations.operationWord,
      effectEvaluator (s := OperationSort.parent) (oldEnvironment stage)
        (incrementEnvironment stage) OperationRelations.operationWord) = _
  simp only [SourceOperationRelations.evaluation, effectEvaluator, OperationRelations.operationWord,
    Finsupp.linearCombination_single, one_smul, oldEnvironment, incrementEnvironment,
    fockOperation_eval, fockOperation_effect]
  rfl

theorem stage_source_factorizes
    {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    stageInventory stage OperationRelations.operationWord =
        ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) ∧
      runtimeFacade.readoutAt runtime .particleWave =
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
      stage.next.current = stage.activated.nextCurrent := by
  have source := stage.factorizes
  have coverage := coversAt_factorizes runtime .particleWave
  exact ⟨stage_reads_installed_payload stage, payload_is_readout runtime, source.2.1,
    coverage.2.2.2.1, source.2.2.1, source.2.2.2⟩

/-- Each finite evaluator is read from the already generated material stages. -/
def prefixEvaluator (depth stage : Nat) : FormalCarrier →ₗ[ℤ] PrefixCarrier stage :=
  SourceOperationRuntime.prefixEvaluator sourceMaterial environmentProjection (runtimeAt depth) stage

def prefixRestriction (stage : Nat) : PrefixCarrier (stage + 1) →ₗ[ℤ] PrefixCarrier stage :=
  SourceOperationRuntime.prefixRestriction stage

/-- The original Fock source directly specializes the common runtime algorithm. -/
def prefixData (depth : Nat) :
    Data (R := ℤ) (Generator := FormalCarrier) (Carrier := PrefixCarrier) :=
  SourceOperationRuntime.prefixData sourceMaterial environmentProjection (runtimeAt depth)

theorem prefix_compatible (depth : Nat) : (prefixData depth).Compatible :=
  SourceOperationRuntime.prefix_compatible sourceMaterial environmentProjection (runtimeAt depth)

def completion (depth : Nat) :=
  SourceOperationRuntime.completion (R := ℤ) (s := OperationSort.parent)
    sourceMaterial environmentProjection (runtimeAt depth)

def completionMap (depth : Nat) :=
  SourceOperationRuntime.completionMap (R := ℤ) (s := OperationSort.parent)
    sourceMaterial environmentProjection (runtimeAt depth)

/-- The existing completion consumes the generated compatibility square. -/
theorem completion_source_to_prefix (depth stage : Nat) :
    completionMap depth ≫ (prefixData depth).restriction (prefix_compatible depth) stage ≫
        ModuleCat.ofHom ((prefixData depth).stageRealization stage) =
      ModuleCat.ofHom (prefixEvaluator depth stage) :=
  (prefixData depth).source_to_evaluator (prefix_compatible depth) stage

theorem completion_source_to_actual_stage (depth stage : Nat)
    (relation : FormalCarrier) (index : Fin (stage + 1)) :
    ((prefixData depth).stageRealization stage
      (((prefixData depth).restriction (prefix_compatible depth) stage).hom
        ((completionMap depth).hom relation))) index =
      stageInventory ((materialHistory depth stage).stageAt index) relation :=
  SourceOperationRuntime.completion_source_to_actual_stage
    sourceMaterial environmentProjection (runtimeAt depth) stage relation index

theorem completion_word_reads_payload (depth stage : Nat) (index : Fin (stage + 1)) :
    ((prefixData depth).stageRealization stage
      (((prefixData depth).restriction (prefix_compatible depth) stage).hom
        ((completionMap depth).hom OperationRelations.operationWord))) index =
      ((payloadAt ((runtimeAt depth).advance index.val)).sourceState,
        (payloadAt ((runtimeAt depth).advance index.val)).forcedTrace) :=
  (completion_source_to_actual_stage depth stage _ index).trans
    (stage_reads_installed_payload ((materialHistory depth stage).stageAt index))

/-- The full inverse fibre is the joint kernel of every generated finite observation. -/
theorem completion_fibre_iff (depth : Nat) (left right : FormalCarrier) :
    (completionMap depth).hom left = (completionMap depth).hom right ↔
      ∀ stage (index : Fin (stage + 1)),
        stageInventory ((materialHistory depth stage).stageAt index) left =
          stageInventory ((materialHistory depth stage).stageAt index) right :=
  SourceOperationRuntime.completion_fibre_iff
    sourceMaterial environmentProjection (runtimeAt depth) left right

/-- Completion readback and actual-stage authority are consumed together. -/
theorem completion_word_factorizes (depth bound : Nat) (index : Fin (bound + 1)) :
    let stage := (materialHistory depth bound).stageAt index
    let runtime := (runtimeAt depth).advance index.val
    (((prefixData depth).stageRealization bound
      (((prefixData depth).restriction (prefix_compatible depth) bound).hom
        ((completionMap depth).hom OperationRelations.operationWord))) index =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace)) ∧
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
  have source := stage_source_factorizes ((materialHistory depth bound).stageAt index)
  exact ⟨completion_word_reads_payload depth bound index, source.2⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
