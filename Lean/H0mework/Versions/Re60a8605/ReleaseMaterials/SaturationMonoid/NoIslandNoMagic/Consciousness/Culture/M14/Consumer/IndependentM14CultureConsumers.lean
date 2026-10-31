import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface.SourceNativeM14CultureCoordinates
import H0mework.Foundation.Relations.ConsumerQuotient

/-!
# Independent M14 culture consumers

The consumer vocabulary is fixed over the exact two-point occurrence exposed
by the source-native M14 culture interface.  Every read delegates directly to
one low-universe interface coordinate.  In particular, transmission replay
retains the honest publication bit together with the ordered actual support
trace; it is not a Boolean classifier standing in for that trace.

No culture source face, representation, quotient, installation, root, or
successor is imported or constructed here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Consumer

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedActualRelationRoleReflexiveRing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface

noncomputable section

/-- Independent culture readouts.  `memberEvaluation` retains the member
index, so the three local restrictions are distinct consumers. -/
inductive M14CultureConsumer where
  | naming
  | memberEvaluation (member : ThreeCycleTime)
  | jointKernel
  | transmissionReplay
  | gluingResidual
  | practiceMedium
  | sharedLineage
  deriving DecidableEq, Repr

/-- Heterogeneous low-universe output selected only by the consumer name. -/
def M14CultureConsumerOutputAt
    (base : Nat) : M14CultureConsumer → Type _
  | .naming => M14CultureNamingReadout
  | .memberEvaluation _member => M14CultureMemberEvaluationReadout
  | .jointKernel => M14CultureJointKernelBundleReadoutAt base
  | .transmissionReplay => M14CultureTransmissionReplayReadout
  | .gluingResidual => M14CultureGluingReadout
  | .practiceMedium => M14CulturePracticeMediumReadout
  | .sharedLineage => M14CultureSharedLineageReadout

/-- Every consumer read is literally one interface read function. -/
def m14CultureConsumerReadAt
    (base : Nat) :
    (consumer : M14CultureConsumer) → M14CultureOccurrenceAt base →
      M14CultureConsumerOutputAt base consumer
  | .naming => sourceM14CultureNamingRead base
  | .memberEvaluation member =>
      sourceM14CultureMemberEvaluationRead base member
  | .jointKernel => sourceM14CultureJointKernelBundleRead base
  | .transmissionReplay => sourceM14CultureTransmissionReplayRead base
  | .gluingResidual => sourceM14CultureGluingRead base
  | .practiceMedium => sourceM14CulturePracticeMediumRead base
  | .sharedLineage => sourceM14CultureSharedLineageRead base

/-- Nonempty independent family.  Positivity is witnessed by actual
transmission replay rather than a target carrier or quotient. -/
def m14CultureConsumersAt (base : Nat) :
    IndependentConsumerSystem (M14CultureOccurrenceAt base) where
  Consumer := M14CultureConsumer
  Output := M14CultureConsumerOutputAt base
  read := m14CultureConsumerReadAt base
  positive := ⟨.transmissionReplay⟩

/-- Exact C1 source responsibility consumed by each named readout. -/
def M14CultureConsumerGroundedAt
    (base : Nat) : M14CultureConsumer → Prop
  | .naming =>
      type_of%
        (sourceGeneratedM14CultureObserverKernelBundle_directConsumer base)
  | .memberEvaluation _member =>
      type_of%
        (sourceGeneratedM14CultureObserverKernelBundle_directConsumer base)
  | .jointKernel =>
      type_of%
        (sourceGeneratedM14CultureObserverKernelBundle_directConsumer base)
  | .transmissionReplay =>
      type_of%
          (sourceGeneratedM14ActualRelationCultureNetwork_directConsumer base) ∧
        type_of% (sourceGeneratedM14CulturePublication_directConsumer base) ∧
        type_of% (sourceM14CultureTransmissionReplay_grounded base)
  | .gluingResidual =>
      type_of% (sourceGeneratedM14CultureGluingResidual_directConsumer base)
  | .practiceMedium =>
      type_of%
          (sourceGeneratedM14ActualRelationCultureNetwork_directConsumer base) ∧
        (∀ occurrence,
          (sourceM14CulturePracticeMediumRead base occurrence).medium =
              actualRelationCycleTargetRoleAt base .t2 ∧
            (sourceM14CulturePracticeMediumRead base occurrence).effect = 1)
  | .sharedLineage =>
      type_of%
          (sourceGeneratedM14CultureObserverKernelBundle_directConsumer base) ∧
        type_of% (sourceGeneratedM14CulturePublication_directConsumer base)

/-- All consumers are grounded in the existing C1 network, observer kernel,
gluing residual, or honest cycle-memory publication. -/
theorem everyM14CultureConsumer_grounded (base : Nat) :
    ∀ consumer, M14CultureConsumerGroundedAt base consumer := by
  intro consumer
  cases consumer with
  | naming =>
      exact sourceGeneratedM14CultureObserverKernelBundle_directConsumer base
  | memberEvaluation member =>
      exact sourceGeneratedM14CultureObserverKernelBundle_directConsumer base
  | jointKernel =>
      exact sourceGeneratedM14CultureObserverKernelBundle_directConsumer base
  | transmissionReplay =>
      exact
        ⟨sourceGeneratedM14ActualRelationCultureNetwork_directConsumer base,
          sourceGeneratedM14CulturePublication_directConsumer base,
          sourceM14CultureTransmissionReplay_grounded base⟩
  | gluingResidual =>
      exact sourceGeneratedM14CultureGluingResidual_directConsumer base
  | practiceMedium =>
      exact
        ⟨sourceGeneratedM14ActualRelationCultureNetwork_directConsumer base,
          fun occurrence =>
            ⟨sourceM14CulturePracticeMediumRead_medium_exact base occurrence,
              sourceM14CulturePracticeMediumRead_effect_eq_one base
                occurrence⟩⟩
  | sharedLineage =>
      exact
        ⟨sourceGeneratedM14CultureObserverKernelBundle_directConsumer base,
          sourceGeneratedM14CulturePublication_directConsumer base⟩

/-- Replay is faithful because its ordered support trace is `[]` versus
`[t0,t1,t2]`; the proof does not invert the publication bit. -/
theorem m14CultureTransmissionReplayRead_injective (base : Nat) :
    Function.Injective
      ((m14CultureConsumersAt base).read .transmissionReplay) := by
  intro left right replayEq
  apply m14CultureTransmissionTraceRead_injective base
  exact congrArg M14CultureTransmissionReplayReadout.supportTrace replayEq

/-- Direct consumer for the complete independent vocabulary and its actual
transmission witness. -/
theorem independentM14CultureConsumers_directConsumer (base : Nat) :
    Nonempty M14CultureConsumer ∧
      type_of% (everyM14CultureConsumer_grounded base) ∧
      (sourceM14CultureTransmissionReplayRead base true).supportTrace =
        [.t0, .t1, .t2] ∧
      (sourceM14CultureTransmissionReplayRead base false).supportTrace = [] ∧
      Function.Injective
        ((m14CultureConsumersAt base).read .transmissionReplay) :=
  ⟨⟨.transmissionReplay⟩, everyM14CultureConsumer_grounded base,
    sourceM14CultureTransmissionSupportTraceRead_true base,
    sourceM14CultureTransmissionSupportTraceRead_false base,
    m14CultureTransmissionReplayRead_injective base⟩

end
end Consumer
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Consumer.m14CultureConsumerReadAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Consumer.everyM14CultureConsumer_grounded
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Consumer.m14CultureTransmissionReplayRead_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Consumer.independentM14CultureConsumers_directConsumer
