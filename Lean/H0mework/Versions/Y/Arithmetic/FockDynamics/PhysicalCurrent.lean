import H0mework.Foundation.Finite.ProvenanceFlux
import H0mework.Versions.Y.Arithmetic.FockDynamics.AtomicDynamics

/-!
# Occurrence-sensitive physical factor-decay current

A projected effective split is not the complete physical current.  The current
below retains the exact factor-decay occurrence from one fixed origin; its
Fock state is the dependent physical face of that occurrence state.  An actual
incidence carries the classifier-generated effect and all operational
write-back data.  The finite structural channel key is only a projection.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockOccurrencePhysicalProcess

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open ParticleWaveFock
open ParticleWaveFockAtomicProcess

noncomputable section

/-- Complete occurrence current over one fixed factor-decay origin. -/
structure OccurrencePhysicalCurrentAt (index : Nat) : Type where
  private mk ::
  origin : EffectiveSplitAt index
  occurrence : SourceGeneratedFiniteEventIndexedProvenanceFlux.OccurrenceAt
    (factorDecayProcess index) origin

/-- Expose an already source-generated factor-process occurrence as its
physical dependent face.  No state, path or origin is reconstructed. -/
def ofOccurrence {index : Nat} {origin : EffectiveSplitAt index}
    (occurrence : SourceGeneratedFiniteEventIndexedProvenanceFlux.OccurrenceAt
      (factorDecayProcess index) origin) :
    OccurrencePhysicalCurrentAt index :=
  ⟨origin, occurrence⟩

@[simp] theorem ofOccurrence_origin {index : Nat}
    {origin : EffectiveSplitAt index}
    (occurrence : SourceGeneratedFiniteEventIndexedProvenanceFlux.OccurrenceAt
      (factorDecayProcess index) origin) :
    (ofOccurrence occurrence).origin = origin :=
  rfl

@[simp] theorem ofOccurrence_occurrence {index : Nat}
    {origin : EffectiveSplitAt index}
    (occurrence : SourceGeneratedFiniteEventIndexedProvenanceFlux.OccurrenceAt
      (factorDecayProcess index) origin) :
    (ofOccurrence occurrence).occurrence = occurrence :=
  rfl

/-- The physical/Fock state is generated from the occurrence's actual state. -/
def OccurrencePhysicalCurrentAt.physicalCurrent {index : Nat}
    (current : OccurrencePhysicalCurrentAt index) : PhysicalCurrentAt index :=
  generateCurrent current.occurrence.state

@[simp] theorem OccurrencePhysicalCurrentAt.physicalCurrent_state
    {index : Nat} (current : OccurrencePhysicalCurrentAt index) :
    current.physicalCurrent.current = current.occurrence.state :=
  rfl

/-- Initial occurrence and physical current are the fixed origin itself. -/
def seed {index : Nat} (origin : EffectiveSplitAt index) :
    OccurrencePhysicalCurrentAt index :=
  ⟨origin, SourceGeneratedFiniteEventIndexedProvenanceFlux.seed
    (factorDecayProcess index) origin⟩

@[simp] theorem seed_occurrence_state {index : Nat}
    (origin : EffectiveSplitAt index) :
    (seed origin).occurrence.state = origin :=
  rfl

@[simp] theorem seed_physical_state {index : Nat}
    (origin : EffectiveSplitAt index) :
    (seed origin).physicalCurrent.current = origin :=
  rfl

/-- One actual channel advances provenance and projected state together. -/
def OccurrencePhysicalCurrentAt.advance {index : Nat}
    (current : OccurrencePhysicalCurrentAt index)
    (channel : FactorDecayChannelAt current.occurrence.state) :
    OccurrencePhysicalCurrentAt index :=
  ⟨current.origin, current.occurrence.advance channel⟩

@[simp] theorem OccurrencePhysicalCurrentAt.advance_state {index : Nat}
    (current : OccurrencePhysicalCurrentAt index)
    (channel : FactorDecayChannelAt current.occurrence.state) :
    (current.advance channel).occurrence.state = channel.target :=
  rfl

@[simp] theorem OccurrencePhysicalCurrentAt.advance_origin {index : Nat}
    (current : OccurrencePhysicalCurrentAt index)
    (channel : FactorDecayChannelAt current.occurrence.state) :
    (current.advance channel).origin = current.origin :=
  rfl

/-- Finite observer projection of one actual occurrence incidence. -/
def structuralKeyAt {index : Nat}
    (current : OccurrencePhysicalCurrentAt index)
    (channel : FactorDecayChannelAt current.occurrence.state) :
    FactorDecayStructuralChannelKeyAt index :=
  ⟨current.occurrence.state, channel⟩

/-- Complete actual occurrence incidence.  No channel or effect is selected
outside the classifier branch consumed by `generateActualIncidence`. -/
structure ActualOccurrenceFactorDecayAt {index : Nat}
    (source : OccurrencePhysicalCurrentAt index) : Type where
  private mk ::
  sourceOccurrence :
    SourceGeneratedFiniteEventIndexedProvenanceFlux.OccurrenceAt
      (factorDecayProcess index) source.origin
  sourceOccurrence_eq : sourceOccurrence = source.occurrence
  step : GeneratedStepAt source.physicalCurrent
    (generateEvent source.physicalCurrent)
  effect : GeneratedStepEffectAt source.physicalCurrent
    (generateEvent source.physicalCurrent) step
  dynamics_eq : generateDynamics source.physicalCurrent = .step step effect
  operationalReceipt : OperationalFactorDecayChannelReceiptAt step.channel
  operationalReceipt_eq : operationalReceipt = effect.receipt
  fockTrace : GeneratedFactorDecayFockTraceAt step.channel operationalReceipt
  fockTrace_eq : HEq fockTrace effect.fockTrace
  writeBack : SourceGeneratedFiniteEventIndexedResidualProcess.PathWriteBack
    (factorDecayProcess index) operationalReceipt.step.path
  writeBack_eq : writeBack = operationalReceipt.step.writeBack
  lineage : SourceGeneratedFiniteEventIndexedResidualProcess.GeneratedPathAt
    (factorDecayProcess index) source.origin step.channel.target
  lineage_eq : lineage = source.occurrence.history.snoc step.channel
  target : OccurrencePhysicalCurrentAt index
  target_eq : target = source.advance step.channel
  structuralKey : FactorDecayStructuralChannelKeyAt index
  structuralKey_eq : structuralKey = structuralKeyAt source step.channel

/-- Build the complete incidence from the source dynamics' generated step
branch.  Operational and Fock receipts are reused from the same effect. -/
def generateActualIncidence {index : Nat}
    (source : OccurrencePhysicalCurrentAt index)
    (step : GeneratedStepAt source.physicalCurrent
      (generateEvent source.physicalCurrent))
    (effect : GeneratedStepEffectAt source.physicalCurrent
      (generateEvent source.physicalCurrent) step)
    (dynamics_eq : generateDynamics source.physicalCurrent = .step step effect) :
    ActualOccurrenceFactorDecayAt source :=
  { sourceOccurrence := source.occurrence
    sourceOccurrence_eq := rfl
    step := step
    effect := effect
    dynamics_eq := dynamics_eq
    operationalReceipt := effect.receipt
    operationalReceipt_eq := rfl
    fockTrace := effect.fockTrace
    fockTrace_eq := HEq.rfl
    writeBack := effect.receipt.step.writeBack
    writeBack_eq := rfl
    lineage := source.occurrence.history.snoc step.channel
    lineage_eq := rfl
    target := source.advance step.channel
    target_eq := rfl
    structuralKey := structuralKeyAt source step.channel
    structuralKey_eq := rfl }

namespace ActualOccurrenceFactorDecayAt

variable {index : Nat} {source : OccurrencePhysicalCurrentAt index}

theorem target_depth_strict (actual : ActualOccurrenceFactorDecayAt source) :
    source.occurrence.depth < actual.target.occurrence.depth := by
  rw [actual.target_eq]
  exact SourceGeneratedFiniteEventIndexedProvenanceFlux.advance_depth_strict
    source.occurrence actual.step.channel

def advancedOccurrence (actual : ActualOccurrenceFactorDecayAt source) :
    SourceGeneratedFiniteEventIndexedProvenanceFlux.OccurrenceAt
      (factorDecayProcess index) source.origin :=
  source.occurrence.advance actual.step.channel

theorem targetOccurrence_heq (actual : ActualOccurrenceFactorDecayAt source) :
    HEq actual.target.occurrence actual.advancedOccurrence := by
  rw [actual.target_eq]
  rfl

theorem advancedOccurrence_ne (actual : ActualOccurrenceFactorDecayAt source) :
    actual.advancedOccurrence ≠ source.occurrence :=
  SourceGeneratedFiniteEventIndexedProvenanceFlux.advance_ne
    source.occurrence actual.step.channel

theorem target_depth_ne (actual : ActualOccurrenceFactorDecayAt source) :
    actual.target.occurrence.depth ≠ source.occurrence.depth :=
  Nat.ne_of_gt actual.target_depth_strict

theorem target_physical_eq_generated
    (actual : ActualOccurrenceFactorDecayAt source) :
    actual.target.physicalCurrent = actual.step.target := by
  rw [actual.target_eq, actual.step.target_eq]
  rfl

theorem writeBack_recollects_source
    (actual : ActualOccurrenceFactorDecayAt source) :
    (factorDecayProcess index).recollectTrace
        actual.writeBack.live actual.writeBack.trace =
      splitResidual source.occurrence.state := by
  rw [actual.writeBack_eq]
  exact actual.operationalReceipt.writeBack_recollects

theorem structuralKey_is_projection
    (actual : ActualOccurrenceFactorDecayAt source) :
    actual.structuralKey =
      ⟨source.occurrence.state, actual.step.channel⟩ :=
  actual.structuralKey_eq

end ActualOccurrenceFactorDecayAt

end

end ParticleWaveFockOccurrencePhysicalProcess
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
