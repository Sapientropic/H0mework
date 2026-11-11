import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootAtomFieldAuthorityKernel
import H0mework.Realization.Memory.ResidualReadout

/-!
# Root-generated information and memory readout

The effective write already owns one canonical forced trace, path trace and
path-indexed write-back.  This adapter identifies all three with the earlier
`residualInformationReadout` and then reuses the existing P51 memory ontology:
recollectable residual memory is exactly nonzero generated trace.

The root theorem keeps the readout downstream of an exact source-native root
occurrence.  It simultaneously records the root compiler branch and target
commuting law; a free effective-process write cannot acquire root authority by
using the scalar identity alone.

This is deliberately a Mathlib adapter.  It grants no source, event, registry,
receipt or outcome and is not imported by `LivingLawAxiomFreeCore`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution

open EffectiveResidualUpdate
open ResidualProjection

universe u

namespace GeneratedWriteAt

variable {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
variable {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
variable {current : Current C}

/-- The write's forced trace is the early information readout of its exact
source-owned residual. -/
theorem forcedTrace_eq_residualInformationReadout
    (write : GeneratedWriteAt V current) :
    write.trace.forcedTrace =
      residualInformationReadout
        (C.process current.surface).keep current.residual.value := by
  rw [write.trace.forcedTrace_eq, current.residual.value_eq]
  rfl

/-- The genuine native path carries the same information trace. -/
theorem pathTrace_eq_residualInformationReadout
    (write : GeneratedWriteAt V current) :
    (C.process current.surface).toPathIndexedResidualTransport.pathTrace
        write.path =
      residualInformationReadout
        (C.process current.surface).keep current.residual.value := by
  change
    (C.process current.surface).toPathIndexedResidualTransport.pathTrace
        ((C.process current.surface).updatePath current.residual.state 1) =
      residualInformationReadout
        (C.process current.surface).keep current.residual.value
  rw [write.trace.path_trace]
  exact write.forcedTrace_eq_residualInformationReadout

/-- The trace written back by the exact native path is that same readout. -/
theorem writeBackTrace_eq_residualInformationReadout
    (write : GeneratedWriteAt V current) :
    write.writeBack.value.2 =
      residualInformationReadout
        (C.process current.surface).keep current.residual.value := by
  rw [write.writeBack.trace_eq]
  exact write.pathTrace_eq_residualInformationReadout

/-- P51 recollectable memory is present exactly when the root-generated
effective trace is nonzero. -/
theorem recollectableMemoryPotential_iff_forcedTrace_ne_zero
    (write : GeneratedWriteAt V current) :
    RecollectableMemoryPotential
        (residualMemoryAct (C.process current.surface).keep)
        current.residual.value ↔
      write.trace.forcedTrace ≠ 0 := by
  rw [residualMemoryPotential_iff_informationTrace_nonzero,
    ← write.forcedTrace_eq_residualInformationReadout]

end GeneratedWriteAt

namespace ConstructiveRoot

/-- One exact root occurrence generates the structural native branch, its
commuting effective target, the information trace and the corresponding
recollectable-memory criterion in a single mouth. -/
theorem SourceNativeAtomFieldRecognitionAt.rootOccurrence_informationMemoryReadout
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    {current : V.Current}
    (occurrence :
      world.source.restructuringSource.source.toRootSource.actual.OccurrenceAt
        current) :
    let write := recognition.generationLaw.total.write
      (recognition.generationLaw.currentAt current)
    world.source.restructuringSource.source.toRootSource.actual.compile occurrence =
        .nativeWrite (recognition.generationLaw.rootWrite occurrence) ∧
      recognition.generationLaw.currentAt
          (V.nativeTarget (recognition.generationLaw.rootWrite occurrence)) = write.next ∧
      write.trace.forcedTrace =
          residualInformationReadout
            (C.process (recognition.generationLaw.currentAt current).surface).keep
            (recognition.generationLaw.currentAt current).residual.value ∧
      (RecollectableMemoryPotential
          (residualMemoryAct
            (C.process (recognition.generationLaw.currentAt current).surface).keep)
          (recognition.generationLaw.currentAt current).residual.value ↔
        write.trace.forcedTrace ≠ 0) := by
  dsimp only
  let write := recognition.generationLaw.total.write
    (recognition.generationLaw.currentAt current)
  exact ⟨recognition.generationLaw.structural_eq occurrence,
    recognition.generationLaw.target_commutes occurrence,
    write.forcedTrace_eq_residualInformationReadout,
    write.recollectableMemoryPotential_iff_forcedTrace_ne_zero⟩

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
