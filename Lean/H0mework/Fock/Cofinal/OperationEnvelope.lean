import H0mework.Fock.Cofinal.OperationPrefix
import H0mework.Realization.Perfectification.ScalarEnvelope
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The original material history generates a faithful completed evaluation from its
canonical source coordinates, then consumes the existing exact-envelope producer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationEnvelope

open ParticleWaveFock ParticleWaveFockOperationPrefix
open SourceGeneratedScalarPerfectification SourceGeneratedScalarExactEnvelope
open CategoryTheory

noncomputable section

abbrev ScaleIndex := Units NNReal
abbrev ParentIndex := (ScaleIndex ⊕ ScaleIndex) ⊕ (ScaleIndex × ScaleIndex)
abbrev PairIndex := ParentIndex ⊕ ParentIndex

def oneParticleBasis : Module.Basis ScaleIndex ℤ IntegralOneParticle :=
  SourceGeneratedIntegralCharacterGroupRing.canonicalBasis

def parentBasis : Module.Basis ParentIndex ℤ ParentCarrier :=
  (oneParticleBasis.prod oneParticleBasis).prod (oneParticleBasis.tensorProduct oneParticleBasis)

def pairBasis : Module.Basis PairIndex ℤ (ParentCarrier × ParentCarrier) :=
  parentBasis.prod parentBasis

abbrev ProbeIndex := Σ bound : Nat, Fin (bound + 1) × PairIndex
abbrev Observer := ProbeIndex →₀ ℤ

def stageRead (depth bound : Nat) : completion depth →ₗ[ℤ] PrefixCarrier bound :=
  SourceOperationRuntime.stageRead (R := ℤ) (s := OperationSort.parent)
    sourceMaterial environmentProjection (ParticleWaveFockRuntime.runtimeAt depth) bound

def probeRead (depth : Nat) (probe : ProbeIndex) : Module.Dual ℤ (completion depth) :=
  (pairBasis.coord probe.2.2).comp
    ((LinearMap.proj probe.2.1).comp (stageRead depth probe.1))

/-- Finite source coordinate tests generate the completed evaluation. -/
def completedEvaluation (depth : Nat) : completion depth →ₗ[ℤ] Module.Dual ℤ Observer :=
  (Finsupp.linearCombination ℤ (probeRead depth)).flip

theorem completedEvaluation_single (depth : Nat)
    (value : completion depth) (probe : ProbeIndex) :
    completedEvaluation depth value (Finsupp.single probe 1) =
      pairBasis.repr (stageRead depth probe.1 value probe.2.1) probe.2.2 := by
  simp only [completedEvaluation, LinearMap.flip_apply, Finsupp.linearCombination_single,
    one_smul]
  rfl

theorem completedEvaluation_injective (depth : Nat) :
    Function.Injective (completedEvaluation depth) := by
  intro left right observed
  apply Limits.Concrete.limit_ext ((prefixData depth).quotientTower (prefix_compatible depth))
  intro bound
  apply (prefixData depth).stageRealization_injective bound.unop
  change stageRead depth bound.unop left = stageRead depth bound.unop right
  funext index
  apply pairBasis.repr.injective
  ext coordinate
  have reading := LinearMap.congr_fun observed
    (Finsupp.single (⟨bound.unop, index, coordinate⟩ : ProbeIndex) 1)
  simpa only [completedEvaluation_single] using reading

theorem completedEvaluation_kernel (depth : Nat) :
    LinearMap.ker (completedEvaluation depth) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (completedEvaluation_injective depth)

/-- The existing generic producer owns every exact-envelope output. -/
def generatedEnvelope (depth : Nat) : UniversalPerfectEnvelope (completedEvaluation depth) :=
  sourceGeneratedPerfectification (completedEvaluation depth)

def sourceMap (depth : Nat) :
    FormalCarrier →ₗ[ℤ] SourceGeneratedScalarExactEnvelope.Carrier (completedEvaluation depth) :=
  (canonicalMap (completedEvaluation depth)).comp (completionMap depth).hom

theorem envelopeMap_injective (depth : Nat) :
    Function.Injective (canonicalMap (completedEvaluation depth)) := by
  intro left right same
  apply completedEvaluation_injective depth
  exact congrArg (dualEmbedding (completedEvaluation depth)) same

/-- Finite-stage readouts descend through the already generated exact envelope. -/
def envelopeStageRead (depth bound : Nat) :
    SourceGeneratedScalarExactEnvelope.Carrier (completedEvaluation depth) →ₗ[ℤ]
      PrefixCarrier bound :=
  canonicalFactor (completedEvaluation depth) (stageRead depth bound) (by
    rw [completedEvaluation_kernel]
    exact bot_le)

theorem envelopeStageRead_source (depth bound : Nat)
    (word : FormalCarrier) (index : Fin (bound + 1)) :
    envelopeStageRead depth bound (sourceMap depth word) index =
      stageInventory ((materialHistory depth bound).stageAt index) word :=
  completion_source_to_actual_stage depth bound word index

theorem envelope_source_fibre_iff (depth : Nat) (left right : FormalCarrier) :
    sourceMap depth left = sourceMap depth right ↔
      ∀ bound (index : Fin (bound + 1)),
        stageInventory ((materialHistory depth bound).stageAt index) left =
          stageInventory ((materialHistory depth bound).stageAt index) right := by
  constructor
  · intro same
    exact (completion_fibre_iff depth left right).mp (envelopeMap_injective depth same)
  · intro same
    exact congrArg (canonicalMap (completedEvaluation depth))
      ((completion_fibre_iff depth left right).mpr same)

theorem envelope_source_probe (depth : Nat) (word : FormalCarrier) (probe : ProbeIndex) :
    (generatedEnvelope depth).inclusion ((generatedEnvelope depth).map (sourceMap depth word))
        (Finsupp.single probe 1) =
      pairBasis.repr
        (stageInventory ((materialHistory depth probe.1).stageAt probe.2.1) word) probe.2.2 := by
  change completedEvaluation depth ((completionMap depth).hom word) (Finsupp.single probe 1) = _
  exact (completedEvaluation_single depth ((completionMap depth).hom word) probe).trans
    (congrArg (fun value => pairBasis.repr value probe.2.2)
      (completion_source_to_actual_stage depth probe.1 word probe.2.1))

theorem envelope_word_factorizes (depth bound : Nat) (index : Fin (bound + 1)) :
    let stage := (materialHistory depth bound).stageAt index
    let runtime := (ParticleWaveFockRuntime.runtimeAt depth).advance index.val
    envelopeStageRead depth bound (sourceMap depth OperationRelations.operationWord) index =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) ∧
    (ParticleWaveFockRuntime.runtimeFacade.readoutAt runtime .particleWave =
        .inl ⟨activeAt runtime, payloadAt runtime⟩ ∧
      stage.activated.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq (ParticleWaveFockRuntime.runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((ParticleWaveFockRuntime.runtimeFacade.installationAt runtime .particleWave).embed
            (ParticleWaveFockRuntime.runtimeFacade.projectionAt runtime .particleWave))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent) := by
  have source := completion_word_factorizes depth bound index
  exact ⟨(envelopeStageRead_source depth bound _ index).trans
    (stage_reads_installed_payload ((materialHistory depth bound).stageAt index)), source.2⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationEnvelope
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
