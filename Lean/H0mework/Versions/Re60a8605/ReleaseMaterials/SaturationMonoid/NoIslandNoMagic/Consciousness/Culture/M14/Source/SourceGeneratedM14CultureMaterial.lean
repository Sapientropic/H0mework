import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface.SourceNativeM14CultureCoordinates
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.SharedKernel.SourceGeneratedM14CultureObserverKernelBundle
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Gluing.SourceGeneratedM14CultureGluingResidual

/-!
# Source-generated material for the M14 culture chart

One exact occurrence selected by the existing cycle-memory refinement reads
the local actor/evaluations, common observer kernel, actual transmission
replay, gluing residual, practice medium, and shared lineage.  The source mouth
retains the already generated communication, observer, and gluing bundles; it
does not accept a culture quotient, consumer coverage theorem, factorization,
institutional revision, root update, or successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Source

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution
open Lifecycle Universal Relations
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.SharedKernel
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Gluing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface

noncomputable section

/-- The concrete fixed-chart carrier.  The coordinates retain their distinct
source responsibilities; no algebraic independence is asserted. -/
structure SourceGeneratedM14CultureFaceAt (base : Nat) : Type where
  naming : M14CultureNamingReadout
  memberEvaluation : ThreeCycleTime → M14CultureMemberEvaluationReadout
  jointKernelBundle : M14CultureJointKernelBundleReadoutAt base
  transmissionReplay : M14CultureTransmissionReplayReadout
  gluing : M14CultureGluingReadout
  practiceMedium : M14CulturePracticeMediumReadout
  sharedLineage : M14CultureSharedLineageReadout

def m14CultureFaceReadAt
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) :
    SourceGeneratedM14CultureFaceAt base where
  naming := sourceM14CultureNamingRead base occurrence
  memberEvaluation := fun member =>
    sourceM14CultureMemberEvaluationRead base member occurrence
  jointKernelBundle :=
    sourceM14CultureJointKernelBundleRead base occurrence
  transmissionReplay :=
    sourceM14CultureTransmissionReplayRead base occurrence
  gluing := sourceM14CultureGluingRead base occurrence
  practiceMedium := sourceM14CulturePracticeMediumRead base occurrence
  sharedLineage := sourceM14CultureSharedLineageRead base occurrence

/-- Private face seal indexed by the exact source restriction. -/
inductive SourceGeneratedM14CultureFaceTokenAt
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) : Type
  | private generated

def generateM14CultureFaceTokenAt
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) :
    SourceGeneratedM14CultureFaceTokenAt base occurrence :=
  .generated

namespace SourceGeneratedM14CultureFaceTokenAt

def read
    {base : Nat} {occurrence : M14CultureOccurrenceAt base}
    (_token : SourceGeneratedM14CultureFaceTokenAt base occurrence) :
    SourceGeneratedM14CultureFaceAt base :=
  m14CultureFaceReadAt base occurrence

end SourceGeneratedM14CultureFaceTokenAt

/-- Complete source mouth for one exact fixed-chart occurrence.  Each large
bundle is the existing C1 producer, while publication and replay are selected
only through the source-generated `exactOccurrence`. -/
structure SourceGeneratedM14CultureMaterialAt
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) : Type 1 where
  private mk ::
  face : SourceGeneratedM14CultureFaceTokenAt base occurrence
  faceExact : face = generateM14CultureFaceTokenAt base occurrence
  exactDepth : Nat
  exactDepthGenerated : exactDepth = sourceM14CultureDepthAt base occurrence
  observerBundle : SourceGeneratedM14CultureObserverKernelBundleAt base
  observerBundleExact : observerBundle =
    sourceGeneratedM14CultureObserverKernelBundleAt base
  gluingBundle : SourceGeneratedM14CultureGluingResidualAt base
  gluingBundleExact : gluingBundle =
    sourceGeneratedM14CultureGluingResidualAt base
  replayDelivery : GeneratedDeliveryAt (M14CultureCommunicationAt base)
    (m14CultureOperationalSourcesAt base) .t0 .t0
  replayDeliveryExact : replayDelivery =
    sourceM14CultureReplayDeliveryAt base occurrence
  publicationExact :
    sourceM14CulturePublicationRead base occurrence = occurrence

def sourceGeneratedM14CultureMaterialAt
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) :
    SourceGeneratedM14CultureMaterialAt base occurrence where
  face := generateM14CultureFaceTokenAt base occurrence
  faceExact := rfl
  exactDepth := sourceM14CultureDepthAt base occurrence
  exactDepthGenerated := rfl
  observerBundle := sourceGeneratedM14CultureObserverKernelBundleAt base
  observerBundleExact := rfl
  gluingBundle := sourceGeneratedM14CultureGluingResidualAt base
  gluingBundleExact := rfl
  replayDelivery := sourceM14CultureReplayDeliveryAt base occurrence
  replayDeliveryExact := rfl
  publicationExact := sourceM14CulturePublicationRead_exact base occurrence

@[simp] theorem sourceGeneratedM14CultureMaterial_faceRead_exact
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) :
    (sourceGeneratedM14CultureMaterialAt base occurrence).face.read =
      m14CultureFaceReadAt base occurrence :=
  rfl

/-- Same language name and current practice do not collapse the exact
history: actual replay, gluing, publication, and action authority remain in
the source face. -/
theorem m14Culture_sameNameAndPractice_differentFace (base : Nat) :
    (m14CultureFaceReadAt base true).naming =
        (m14CultureFaceReadAt base false).naming ∧
      (m14CultureFaceReadAt base true).practiceMedium =
        (m14CultureFaceReadAt base false).practiceMedium ∧
      m14CultureFaceReadAt base true ≠
        m14CultureFaceReadAt base false := by
  refine ⟨sourceM14CultureNamingRead_true_eq_false base,
    sourceM14CulturePracticeMediumRead_true_eq_false base, ?_⟩
  intro sameFace
  have sameTrace := congrArg
    (fun face : SourceGeneratedM14CultureFaceAt base =>
      face.transmissionReplay.supportTrace) sameFace
  exact sourceM14CultureTransmissionSupportTraceRead_true_ne_false base
    sameTrace

/-- Direct consumer of the source mouth.  The three C1 producers and the
honest occurrence-selected replay remain separately visible. -/
theorem sourceGeneratedM14CultureMaterial_directConsumer
    (base : Nat) (occurrence : M14CultureOccurrenceAt base) :
    let material := sourceGeneratedM14CultureMaterialAt base occurrence
    Nonempty (SourceGeneratedM14CultureMaterialAt base occurrence) ∧
      material.face.read = m14CultureFaceReadAt base occurrence ∧
      material.exactDepth = sourceM14CultureDepthAt base occurrence ∧
      material.observerBundle =
        sourceGeneratedM14CultureObserverKernelBundleAt base ∧
      material.gluingBundle =
        sourceGeneratedM14CultureGluingResidualAt base ∧
      material.replayDelivery =
        sourceM14CultureReplayDeliveryAt base occurrence ∧
      sourceM14CulturePublicationRead base occurrence = occurrence ∧
      type_of% (sourceGeneratedM14ActualRelationCultureNetwork_directConsumer
        base) ∧
      type_of%
        (SharedKernel.sourceGeneratedM14CultureObserverKernelBundle_directConsumer
          base) ∧
      type_of%
        (Gluing.sourceGeneratedM14CultureGluingResidual_directConsumer base) := by
  let material := sourceGeneratedM14CultureMaterialAt base occurrence
  exact ⟨⟨material⟩, rfl, material.exactDepthGenerated,
    material.observerBundleExact, material.gluingBundleExact,
    material.replayDeliveryExact, material.publicationExact,
    sourceGeneratedM14ActualRelationCultureNetwork_directConsumer base,
    SharedKernel.sourceGeneratedM14CultureObserverKernelBundle_directConsumer
      base,
    Gluing.sourceGeneratedM14CultureGluingResidual_directConsumer base⟩

end
end Source
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Source.m14Culture_sameNameAndPractice_differentFace
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Source.sourceGeneratedM14CultureMaterial_directConsumer
