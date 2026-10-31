import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Consumer.IndependentM14CultureConsumers
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Source.SourceGeneratedM14CultureMaterial

/-!
# Exact representation of the fixed M14 culture chart

The independent chart consumers and the source-generated historical bundle
have exactly the same kernel.  The exhaustive direction is proved from the
actual transmission replay trace: the empty and three-event histories recover
the exact two-point occurrence.  Quotient/range equivalence, unique consumer
factorization, minimality, theory uniqueness, and fixed-domain no-hidden
directions are derived only after that bidirectional theorem.

This is the C2--C4 fixed source chart.  Institutional authority and its actual
U8 revision are a later source extension, not a premise smuggled into this
kernel.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Representation

open ProcessGame Society
open Lifecycle Universal Relations
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Source

noncomputable section

theorem m14CultureFaceRead_injective (base : Nat) :
    Function.Injective (m14CultureFaceReadAt base) := by
  intro left right sameFace
  apply m14CultureTransmissionTraceRead_injective base
  exact congrArg
    (fun face : SourceGeneratedM14CultureFaceAt base =>
      face.transmissionReplay.supportTrace) sameFace

/-- Bidirectional consumer-kernel exactness.  In particular, exhaustiveness
is an output of the actual replay consumer rather than an input certificate. -/
theorem m14CultureKernelExactAt (base : Nat) :
    FaceKernelExactAt (m14CultureConsumersAt base)
      (m14CultureFaceReadAt base) := by
  intro left right
  constructor
  · intro sameFace consumer
    cases consumer with
    | naming =>
        exact congrArg SourceGeneratedM14CultureFaceAt.naming sameFace
    | memberEvaluation member =>
        exact congrFun
          (congrArg SourceGeneratedM14CultureFaceAt.memberEvaluation
            sameFace) member
    | jointKernel =>
        exact congrArg SourceGeneratedM14CultureFaceAt.jointKernelBundle
          sameFace
    | transmissionReplay =>
        exact congrArg SourceGeneratedM14CultureFaceAt.transmissionReplay
          sameFace
    | gluingResidual =>
        exact congrArg SourceGeneratedM14CultureFaceAt.gluing sameFace
    | practiceMedium =>
        exact congrArg SourceGeneratedM14CultureFaceAt.practiceMedium
          sameFace
    | sharedLineage =>
        exact congrArg SourceGeneratedM14CultureFaceAt.sharedLineage
          sameFace
  · intro sameConsumers
    have replayEquality := sameConsumers .transmissionReplay
    have traceEquality := congrArg
      M14CultureTransmissionReplayReadout.supportTrace replayEquality
    have occurrenceEquality :=
      m14CultureTransmissionTraceRead_injective base traceEquality
    subst right
    rfl

noncomputable def m14CultureQuotientEquivRangeAt (base : Nat) :
    (m14CultureConsumersAt base).Quotient ≃
      Set.range (m14CultureFaceReadAt base) :=
  (m14CultureKernelExactAt base).quotientEquivRange

theorem m14CultureEveryConsumer_uniqueFactorizationAt
    (base : Nat) (consumer : M14CultureConsumer) :
    ∃! factor : Set.range (m14CultureFaceReadAt base) →
        M14CultureConsumerOutputAt base consumer,
      ∀ occurrence,
        factor ⟨m14CultureFaceReadAt base occurrence, occurrence, rfl⟩ =
          (m14CultureConsumersAt base).read consumer occurrence :=
  (m14CultureKernelExactAt base
    ).everyConsumer_unique_factorization consumer

/-- The fixed chart face is occurrence-complete: every readout already
defined on this exact source restriction has one unique factorization. -/
theorem m14CultureEveryCurrentReadout_uniqueFactorizationAt
    (base : Nat) {Output : Type*}
    (readout : M14CultureOccurrenceAt base → Output) :
    ∃! factor : Set.range (m14CultureFaceReadAt base) → Output,
      ∀ occurrence,
        factor ⟨m14CultureFaceReadAt base occurrence, occurrence, rfl⟩ =
          readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (m14CultureFaceRead_injective base) readout

/-- Every alternate complete carrier for the same independent chart
consumers is uniquely equivalent over the same exact occurrences. -/
theorem m14CultureCompleteCarrier_uniqueIsoAt
    (base : Nat) {Alternate : Type*}
    (alternate : M14CultureOccurrenceAt base → Alternate)
    (alternateExact : FaceKernelExactAt
      (m14CultureConsumersAt base) alternate) :
    ∃! equivalence : Set.range (m14CultureFaceReadAt base) ≃
        Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨m14CultureFaceReadAt base occurrence, occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ := by
  let canonical := m14CultureKernelExactAt base
  refine ⟨canonical.completeCarrierEquiv alternateExact,
    canonical.completeCarrierEquiv_commutes alternateExact, ?_⟩
  intro candidate commutes
  exact canonical.completeCarrierEquiv_unique
    alternateExact candidate commutes

theorem m14Culture_noHiddenDirectionAt
    (base : Nat) {left right : M14CultureOccurrenceAt base}
    (different :
      m14CultureFaceReadAt base left ≠ m14CultureFaceReadAt base right) :
    ¬ (m14CultureConsumersAt base).Indistinguishable left right :=
  (m14CultureKernelExactAt base).noHiddenDirection different

/-! ## C4 historical identity and hostile same-label controls -/

/-- Historical culture identity retains the common observer kernel, actual
transmission graph, gluing/H¹ state, current practice, exact authority, and
shared lineage on the same source restriction. -/
structure M14CultureHistoricalIdentityAt
    (base : Nat) (left right : M14CultureOccurrenceAt base) : Prop where
  kernelBundle :
    sourceM14CultureJointKernelBundleRead base left =
      sourceM14CultureJointKernelBundleRead base right
  transmissionGraph :
    sourceM14CultureTransmissionSupportTraceRead base left =
      sourceM14CultureTransmissionSupportTraceRead base right
  gluing :
    sourceM14CultureGluingRead base left =
      sourceM14CultureGluingRead base right
  practiceMedium :
    sourceM14CulturePracticeMediumRead base left =
      sourceM14CulturePracticeMediumRead base right
  authority :
    (sourceM14CultureSharedLineageRead base left).actionOccurrenceK =
      (sourceM14CultureSharedLineageRead base right).actionOccurrenceK
  sharedLineage :
    sourceM14CultureSharedLineageRead base left =
      sourceM14CultureSharedLineageRead base right

theorem m14CultureFaceEquality_iff_historicalIdentityAt
    (base : Nat) (left right : M14CultureOccurrenceAt base) :
    m14CultureFaceReadAt base left = m14CultureFaceReadAt base right ↔
      M14CultureHistoricalIdentityAt base left right := by
  constructor
  · intro sameFace
    have occurrenceEquality := m14CultureFaceRead_injective base sameFace
    subst right
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro identity
    have occurrenceEquality :=
      m14CultureTransmissionTraceRead_injective base
        identity.transmissionGraph
    subst right
    rfl

/-- Same name, all member evaluations, common kernel, and current practice
still fail cultural identity when the actual transmission history, gluing,
publication, and authority occurrence differ. -/
theorem m14Culture_sameLabelCurrentPractice_notIdentity (base : Nat) :
    sourceM14CultureNamingRead base true =
        sourceM14CultureNamingRead base false ∧
      (∀ member,
        sourceM14CultureMemberEvaluationRead base member true =
          sourceM14CultureMemberEvaluationRead base member false) ∧
      sourceM14CultureJointKernelBundleRead base true =
        sourceM14CultureJointKernelBundleRead base false ∧
      sourceM14CulturePracticeMediumRead base true =
        sourceM14CulturePracticeMediumRead base false ∧
      ¬ M14CultureHistoricalIdentityAt base true false ∧
      ¬ (m14CultureConsumersAt base).Indistinguishable true false := by
  rcases sourceM14CultureSameNamingEvaluationPractice_differentTraceAndK base
    with ⟨sameName, sameMembers, sameKernel, samePractice,
      differentTrace, _differentAuthority⟩
  have differentFace :
      m14CultureFaceReadAt base true ≠
        m14CultureFaceReadAt base false := by
    intro sameFace
    exact differentTrace (congrArg
      (fun face : SourceGeneratedM14CultureFaceAt base =>
        face.transmissionReplay.supportTrace) sameFace)
  refine ⟨sameName, sameMembers, sameKernel, samePractice, ?_,
    m14Culture_noHiddenDirectionAt base differentFace⟩
  intro identity
  exact differentTrace identity.transmissionGraph

@[simp] theorem m14CultureSourceFace_read_exact
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) :
    (sourceGeneratedM14CultureMaterialAt base occurrence).face.read =
      m14CultureFaceReadAt base occurrence :=
  rfl

/-- One direct mouth for the C2--C4 fixed-chart checkpoint. -/
theorem m14CultureRepresentation_directConsumer
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) :
    type_of% (sourceGeneratedM14CultureMaterial_directConsumer
      base occurrence) ∧
      (∀ consumer,
        M14CultureConsumerGroundedAt base consumer) ∧
      type_of% (m14CultureKernelExactAt base) ∧
      Nonempty ((m14CultureConsumersAt base).Quotient ≃
        Set.range (m14CultureFaceReadAt base)) ∧
      (∀ consumer,
        type_of% (m14CultureEveryConsumer_uniqueFactorizationAt
          base consumer)) ∧
      type_of% (m14CultureSourceFace_read_exact base occurrence) ∧
      type_of% (m14Culture_sameLabelCurrentPractice_notIdentity base) :=
  ⟨sourceGeneratedM14CultureMaterial_directConsumer base occurrence,
    everyM14CultureConsumer_grounded base,
    m14CultureKernelExactAt base,
    ⟨m14CultureQuotientEquivRangeAt base⟩,
    m14CultureEveryConsumer_uniqueFactorizationAt base,
    m14CultureSourceFace_read_exact base occurrence,
    m14Culture_sameLabelCurrentPractice_notIdentity base⟩

end
end Representation
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation.m14CultureKernelExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation.m14CultureQuotientEquivRangeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation.m14CultureEveryConsumer_uniqueFactorizationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation.m14CultureCompleteCarrier_uniqueIsoAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation.m14CultureFaceEquality_iff_historicalIdentityAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation.m14CultureRepresentation_directConsumer
