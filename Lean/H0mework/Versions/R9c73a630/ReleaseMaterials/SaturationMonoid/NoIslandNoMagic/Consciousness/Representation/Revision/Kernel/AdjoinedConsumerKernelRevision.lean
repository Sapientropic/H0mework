import H0mework.Foundation.Relations.ConsumerQuotient

/-!
# Source-independent adjoined consumer-kernel revision

An old exact consumer kernel, a source-owned restriction into a new
occurrence domain, and one concrete escape pair determine the revised
mathematical kernel.  This layer derives old-factorization failure, the
adjoined quotient, updated unique factorization, and complete-carrier
comparison.  It contains no root, failure face, U8, whole-ledger, first write,
or generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Representation
namespace Revision
namespace Kernel

universe uOldOccurrence uOccurrence uReadout uFace uAlternate uReceipt

/-- A real kernel escape with no source-generated actual receipt has no U8
standing.  This status preserves the diagnostic; it neither rejects the
readout nor manufactures a root revision. -/
structure UnsupportedKernelEscapeWithoutReceiptAt
    {Occurrence : Type uOccurrence}
    {Face : Type uFace} {face : Occurrence → Face}
    {newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence}
    (ActualReceipt : Type uReceipt) : Prop where
  escape : FaceKernelEscapeAt face newReadout
  receiptEmpty : IsEmpty ActualReceipt

theorem UnsupportedKernelEscapeWithoutReceiptAt.noActualReceipt
    {Occurrence : Type uOccurrence}
    {Face : Type uFace} {face : Occurrence → Face}
    {newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence}
    {ActualReceipt : Type uReceipt}
    (unsupported : UnsupportedKernelEscapeWithoutReceiptAt
      (face := face) (newReadout := newReadout) ActualReceipt) :
    ActualReceipt → False :=
  unsupported.receiptEmpty.false

/-- Zero-choice diagnostic indexed by an old exact face, a new source domain,
and one actual kernel-escape witness.  No revised carrier is an input. -/
structure KernelExtensionDiagnosticAt
    {OldOccurrence : Type uOldOccurrence}
    {Occurrence : Type uOccurrence}
    (oldSystem : IndependentConsumerSystem.{uOldOccurrence, uReadout}
      OldOccurrence)
    {Face : Type uFace} (oldFace : OldOccurrence → Face)
    (oldExact : FaceKernelExactAt oldSystem oldFace)
    (oldView : Occurrence → OldOccurrence)
    (newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence)
    (escape : FaceKernelEscapeAt (oldFace ∘ oldView) newReadout) : Type where
  private mk ::

namespace KernelExtensionDiagnosticAt

variable {OldOccurrence : Type uOldOccurrence}
variable {Occurrence : Type uOccurrence}
variable {oldSystem : IndependentConsumerSystem.{uOldOccurrence, uReadout}
  OldOccurrence}
variable {Face : Type uFace} {oldFace : OldOccurrence → Face}
variable {oldExact : FaceKernelExactAt oldSystem oldFace}
variable {oldView : Occurrence → OldOccurrence}
variable {newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence}
variable {escape : FaceKernelEscapeAt (oldFace ∘ oldView) newReadout}

def generate
    (oldSystem : IndependentConsumerSystem.{uOldOccurrence, uReadout}
      OldOccurrence)
    (oldFace : OldOccurrence → Face)
    (oldExact : FaceKernelExactAt oldSystem oldFace)
    (oldView : Occurrence → OldOccurrence)
    (newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence)
    (escape : FaceKernelEscapeAt (oldFace ∘ oldView) newReadout) :
    KernelExtensionDiagnosticAt oldSystem oldFace oldExact oldView newReadout
      escape :=
  .mk

variable (diagnostic : KernelExtensionDiagnosticAt oldSystem oldFace oldExact
  oldView newReadout escape)

abbrev reindexedSystem
    (_diagnostic : KernelExtensionDiagnosticAt oldSystem oldFace oldExact
      oldView newReadout escape) :=
  oldSystem.reindex oldView

def restrictedOldFace
    (_diagnostic : KernelExtensionDiagnosticAt oldSystem oldFace oldExact
      oldView newReadout escape) : Occurrence → Face :=
  oldFace ∘ oldView

abbrev revisedSystem
    (_diagnostic : KernelExtensionDiagnosticAt oldSystem oldFace oldExact
      oldView newReadout escape) :=
  (oldSystem.reindex oldView).adjoin newReadout

def revisedFace
    (_diagnostic : KernelExtensionDiagnosticAt oldSystem oldFace oldExact
      oldView newReadout escape) :
    Occurrence → Face × newReadout.Output :=
  refinedFace (oldFace ∘ oldView) newReadout

theorem oldFactorization_isEmpty
    (_diagnostic : KernelExtensionDiagnosticAt oldSystem oldFace oldExact
      oldView newReadout escape) :
    ¬ Function.FactorsThrough newReadout.read (oldFace ∘ oldView) :=
  FaceKernelEscapeAt.not_factorsThrough escape

theorem reindexedOldKernelExact :
    FaceKernelExactAt diagnostic.reindexedSystem diagnostic.restrictedOldFace :=
  FaceKernelExactAt.reindex oldExact oldView

theorem revisedKernelExact :
    FaceKernelExactAt diagnostic.revisedSystem diagnostic.revisedFace :=
  FaceKernelExactAt.adjoin_refinedFace diagnostic.reindexedOldKernelExact

noncomputable def quotientEquivRange :
    diagnostic.revisedSystem.Quotient ≃ Set.range diagnostic.revisedFace :=
  diagnostic.revisedKernelExact.quotientEquivRange

theorem newReadout_uniqueFactorization :
    ∃! factor : Set.range diagnostic.revisedFace → newReadout.Output,
      ∀ occurrence,
        factor ⟨diagnostic.revisedFace occurrence, occurrence, rfl⟩ =
          newReadout.read occurrence :=
  FaceKernelExactAt.newReadout_unique_factorization
    diagnostic.revisedKernelExact

@[simp] theorem revisedFace_projectsOld
    (occurrence : Occurrence) :
    (diagnostic.revisedFace occurrence).1 = oldFace (oldView occurrence) :=
  rfl

theorem everyConsumer_uniqueFactorization
    (consumer : diagnostic.revisedSystem.Consumer) :
    ∃! factor : Set.range diagnostic.revisedFace →
        diagnostic.revisedSystem.Output consumer,
      ∀ occurrence,
        factor ⟨diagnostic.revisedFace occurrence, occurrence, rfl⟩ =
          diagnostic.revisedSystem.read consumer occurrence :=
  diagnostic.revisedKernelExact.everyConsumer_unique_factorization consumer

theorem completeCarrier_uniqueIso
    {Alternate : Type uAlternate}
    (alternate : Occurrence → Alternate)
    (alternateExact : FaceKernelExactAt diagnostic.revisedSystem alternate) :
    ∃! equivalence : Set.range diagnostic.revisedFace ≃ Set.range alternate,
      ∀ occurrence,
        equivalence ⟨diagnostic.revisedFace occurrence, occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ :=
  ⟨diagnostic.revisedKernelExact.completeCarrierEquiv alternateExact,
    diagnostic.revisedKernelExact.completeCarrierEquiv_commutes alternateExact,
    fun candidate commutes =>
      diagnostic.revisedKernelExact.completeCarrierEquiv_unique alternateExact
        candidate commutes⟩

theorem directConsumer :
    ¬ Function.FactorsThrough newReadout.read (oldFace ∘ oldView) ∧
      type_of% diagnostic.revisedKernelExact ∧
      Nonempty (diagnostic.revisedSystem.Quotient ≃
        Set.range diagnostic.revisedFace) ∧
      type_of% diagnostic.newReadout_uniqueFactorization ∧
      (∀ consumer,
        type_of% (diagnostic.everyConsumer_uniqueFactorization consumer)) :=
  ⟨diagnostic.oldFactorization_isEmpty,
    diagnostic.revisedKernelExact,
    ⟨diagnostic.quotientEquivRange⟩,
    diagnostic.newReadout_uniqueFactorization,
    diagnostic.everyConsumer_uniqueFactorization⟩

end KernelExtensionDiagnosticAt
end Kernel
end Revision
end Representation
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.Revision.Kernel.KernelExtensionDiagnosticAt.oldFactorization_isEmpty
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.Revision.Kernel.KernelExtensionDiagnosticAt.revisedKernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.Revision.Kernel.KernelExtensionDiagnosticAt.directConsumer
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.Revision.Kernel.UnsupportedKernelEscapeWithoutReceiptAt.noActualReceipt
