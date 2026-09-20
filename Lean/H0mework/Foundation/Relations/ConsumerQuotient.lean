import Mathlib.Data.Setoid.Basic

/-!
# Independent-consumer quotients and complete concept carriers

The consumer system is fixed before a candidate concept face is named.  Its
joint observational relation is therefore independent of every concrete
carrier.  A separately proved bidirectional kernel theorem identifies that
relation with the kernel of one source-generated face.  The ordinary first
isomorphism theorem then yields the consumer quotient/range equivalence,
unique factorization of every registered consumer, and the unique commuting
equivalence between any two complete carriers.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Representation

universe uOccurrence uOldOccurrence uNewOccurrence uReadout uFace uAlternate

/-- A nonempty family of heterogeneous consumers.  This structure has no
face, carrier, factorization, quotient, or target theorem field. -/
structure IndependentConsumerSystem (Occurrence : Type uOccurrence) where
  Consumer : Type uReadout
  Output : Consumer → Type uReadout
  read : (consumer : Consumer) → Occurrence → Output consumer
  positive : Nonempty Consumer

namespace IndependentConsumerSystem

variable {Occurrence : Type uOccurrence}
variable (system : IndependentConsumerSystem.{uOccurrence, uReadout}
  Occurrence)

/-- Two occurrences are indistinguishable exactly when every independently
registered consumer returns the same result. -/
def Indistinguishable (left right : Occurrence) : Prop :=
  ∀ consumer, system.read consumer left = system.read consumer right

theorem indistinguishable_refl (occurrence : Occurrence) :
    system.Indistinguishable occurrence occurrence :=
  fun _ => rfl

theorem indistinguishable_symm {left right : Occurrence}
    (same : system.Indistinguishable left right) :
    system.Indistinguishable right left :=
  fun consumer => (same consumer).symm

theorem indistinguishable_trans {left middle right : Occurrence}
    (first : system.Indistinguishable left middle)
    (second : system.Indistinguishable middle right) :
    system.Indistinguishable left right :=
  fun consumer => (first consumer).trans (second consumer)

def setoid : Setoid Occurrence where
  r := system.Indistinguishable
  iseqv := ⟨system.indistinguishable_refl,
    system.indistinguishable_symm, system.indistinguishable_trans⟩

/-- The abstract consumer quotient. -/
abbrev Quotient := _root_.Quotient system.setoid

/-- Restrict an established consumer family along an occurrence map generated
by a later source transition.  No new consumer is introduced here. -/
def reindex
    {OldOccurrence : Type uOldOccurrence}
    {NewOccurrence : Type uNewOccurrence}
    (system : IndependentConsumerSystem.{uOldOccurrence, uReadout}
      OldOccurrence)
    (oldView : NewOccurrence → OldOccurrence) :
    IndependentConsumerSystem.{uNewOccurrence, uReadout} NewOccurrence where
  Consumer := system.Consumer
  Output := system.Output
  read := fun consumer => system.read consumer ∘ oldView
  positive := system.positive

@[simp] theorem reindex_indistinguishable_iff
    {OldOccurrence : Type uOldOccurrence}
    {NewOccurrence : Type uNewOccurrence}
    (system : IndependentConsumerSystem.{uOldOccurrence, uReadout}
      OldOccurrence)
    (oldView : NewOccurrence → OldOccurrence)
    (left right : NewOccurrence) :
    (system.reindex oldView).Indistinguishable left right ↔
      system.Indistinguishable (oldView left) (oldView right) :=
  Iff.rfl

end IndependentConsumerSystem

/-- One independently declared readout on an occurrence domain.  This object
contains no carrier, factorization, quotient, failure, or U8 witness. -/
structure IndependentReadout (Occurrence : Type uOccurrence) where
  Output : Type uReadout
  read : Occurrence → Output

namespace IndependentConsumerSystem

/-- Extend a nonempty consumer family by one independently defined readout. -/
def adjoin
    {Occurrence : Type uOccurrence}
    (system : IndependentConsumerSystem.{uOccurrence, uReadout} Occurrence)
    (newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence) :
    IndependentConsumerSystem.{uOccurrence, uReadout} Occurrence where
  Consumer := system.Consumer ⊕ PUnit
  Output
    | .inl consumer => system.Output consumer
    | .inr _ => newReadout.Output
  read
    | .inl consumer => system.read consumer
    | .inr _ => newReadout.read
  positive := by
    rcases system.positive with ⟨consumer⟩
    exact ⟨.inl consumer⟩

theorem adjoin_indistinguishable_iff
    {Occurrence : Type uOccurrence}
    (system : IndependentConsumerSystem.{uOccurrence, uReadout} Occurrence)
    (newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence)
    (left right : Occurrence) :
    (system.adjoin newReadout).Indistinguishable left right ↔
      system.Indistinguishable left right ∧
        newReadout.read left = newReadout.read right := by
  constructor
  · intro same
    exact ⟨fun consumer => same (.inl consumer),
      same (.inr PUnit.unit)⟩
  · rintro ⟨oldSame, newSame⟩ consumer
    cases consumer with
    | inl consumer => exact oldSame consumer
    | inr _ => exact newSame

end IndependentConsumerSystem

/-- A concrete new consumer escapes the kernel of the old face.  This is a
diagnostic statement; by itself it does not generate source or U8 authority. -/
def FaceKernelEscapeAt
    {Occurrence : Type uOccurrence} {Face : Type uFace}
    (face : Occurrence → Face)
    (newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence) : Prop :=
  ∃ left right,
    face left = face right ∧
      newReadout.read left ≠ newReadout.read right

theorem FaceKernelEscapeAt.not_factorsThrough
    {Occurrence : Type uOccurrence} {Face : Type uFace}
    {face : Occurrence → Face}
    {newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence}
    (escape : FaceKernelEscapeAt face newReadout) :
    ¬ Function.FactorsThrough newReadout.read face := by
  intro factors
  rcases escape with ⟨left, right, oldSame, newDifferent⟩
  exact newDifferent (factors oldSame)

/-- Mathematical normal form of a face refined by one new consumer.  An
actual U8 implementation must separately prove that its revised source face
has this kernel; this product does not mint that implementation. -/
def refinedFace
    {Occurrence : Type uOccurrence} {Face : Type uFace}
    (face : Occurrence → Face)
    (newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence) :
    Occurrence → Face × newReadout.Output :=
  fun occurrence => (face occurrence, newReadout.read occurrence)

/-- Bidirectional exactness of a concrete source-generated face.  The
consumer-safe and consumer-exhaustive directions are both theorem output. -/
abbrev FaceKernelExactAt
    {Occurrence : Type uOccurrence}
    (system : IndependentConsumerSystem.{uOccurrence, uReadout} Occurrence)
    {Face : Type uFace} (face : Occurrence → Face) : Prop :=
  ∀ left right,
    face left = face right ↔ system.Indistinguishable left right

namespace FaceKernelExactAt

variable {Occurrence : Type uOccurrence}
variable {system : IndependentConsumerSystem.{uOccurrence, uReadout}
  Occurrence}
variable {Face : Type uFace} {face : Occurrence → Face}

/-- Exactness is stable under a source-owned restriction from a new
occurrence domain to the old one. -/
theorem reindex
    {OldOccurrence : Type uOldOccurrence}
    {NewOccurrence : Type uNewOccurrence}
    {oldSystem : IndependentConsumerSystem.{uOldOccurrence, uReadout}
      OldOccurrence}
    {OldFace : Type uFace} {oldFace : OldOccurrence → OldFace}
    (exact : FaceKernelExactAt oldSystem oldFace)
    (oldView : NewOccurrence → OldOccurrence) :
    FaceKernelExactAt (oldSystem.reindex oldView) (oldFace ∘ oldView) := by
  intro left right
  exact exact (oldView left) (oldView right)

/-- Adjoining one independent consumer and its coordinate gives the exact
refined kernel.  This is the mathematical target an actual revised source
carrier must realize. -/
theorem adjoin_refinedFace
    {newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence}
    (exact : FaceKernelExactAt system face) :
    FaceKernelExactAt (system.adjoin newReadout)
      (refinedFace face newReadout) := by
  intro left right
  rw [system.adjoin_indistinguishable_iff newReadout left right]
  constructor
  · intro same
    exact ⟨(exact left right).1 (congrArg Prod.fst same),
      congrArg Prod.snd same⟩
  · rintro ⟨oldSame, newSame⟩
    exact Prod.ext ((exact left right).2 oldSame) newSame

theorem setoid_rel_iff_ker (exact : FaceKernelExactAt system face)
    (left right : Occurrence) :
    system.setoid.r left right ↔ (Setoid.ker face).r left right :=
  (exact left right).symm

/-- First isomorphism theorem for a concrete concept face. -/
noncomputable def quotientEquivRange
    (exact : FaceKernelExactAt system face) :
    system.Quotient ≃ Set.range face :=
  (Quotient.congrRight exact.setoid_rel_iff_ker).trans
    (Setoid.quotientKerEquivRange face)

@[simp] theorem quotientEquivRange_mk
    (exact : FaceKernelExactAt system face) (occurrence : Occurrence) :
    exact.quotientEquivRange (Quotient.mk system.setoid occurrence) =
      ⟨face occurrence, occurrence, rfl⟩ := by
  apply Subtype.ext
  rfl

def quotientRead (consumer : system.Consumer) :
    system.Quotient → system.Output consumer :=
  Quotient.lift (system.read consumer) (fun _ _ same => same consumer)

noncomputable def factor (exact : FaceKernelExactAt system face)
    (consumer : system.Consumer) :
    Set.range face → system.Output consumer :=
  quotientRead (system := system) consumer ∘ exact.quotientEquivRange.symm

theorem factor_commutes (exact : FaceKernelExactAt system face)
    (consumer : system.Consumer) (occurrence : Occurrence) :
    exact.factor consumer ⟨face occurrence, occurrence, rfl⟩ =
      system.read consumer occurrence := by
  change quotientRead (system := system) consumer
      (exact.quotientEquivRange.symm
        ⟨face occurrence, occurrence, rfl⟩) = _
  rw [← exact.quotientEquivRange_mk occurrence]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem factor_unique (exact : FaceKernelExactAt system face)
    (consumer : system.Consumer)
    (candidate : Set.range face → system.Output consumer)
    (commutes : ∀ occurrence,
      candidate ⟨face occurrence, occurrence, rfl⟩ =
        system.read consumer occurrence) :
    candidate = exact.factor consumer := by
  funext point
  rcases point.property with ⟨occurrence, occurrence_eq⟩
  have point_eq : point = ⟨face occurrence, occurrence, rfl⟩ :=
    Subtype.ext occurrence_eq.symm
  rw [point_eq, commutes occurrence,
    exact.factor_commutes consumer occurrence]

/-- Every registered consumer has exactly one readout on the concrete face
range which commutes with the canonical face map. -/
theorem everyConsumer_unique_factorization
    (exact : FaceKernelExactAt system face)
    (consumer : system.Consumer) :
    ∃! factor : Set.range face → system.Output consumer,
      ∀ occurrence,
        factor ⟨face occurrence, occurrence, rfl⟩ =
          system.read consumer occurrence :=
  ⟨exact.factor consumer, exact.factor_commutes consumer,
    fun candidate commutes => exact.factor_unique consumer candidate commutes⟩

/-- In every exact revised carrier the newly admitted consumer has one unique
factorization. -/
theorem newReadout_unique_factorization
    {newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence}
    {Revised : Type uAlternate} {revisedFace : Occurrence → Revised}
    (revisedExact :
      FaceKernelExactAt (system.adjoin newReadout) revisedFace) :
    ∃! factor : Set.range revisedFace → newReadout.Output,
      ∀ occurrence,
        factor ⟨revisedFace occurrence, occurrence, rfl⟩ =
          newReadout.read occurrence :=
  revisedExact.everyConsumer_unique_factorization (.inr PUnit.unit)

/-- A concrete face difference cannot be hidden from the whole registered
consumer family. -/
theorem noHiddenDirection
    (exact : FaceKernelExactAt system face)
    {left right : Occurrence} (different : face left ≠ face right) :
    ¬ system.Indistinguishable left right := by
  intro invisible
  exact different ((exact left right).2 invisible)

/-! ## Arbitrary readouts of an injective complete occurrence face -/

variable {AnyOutput : Type uReadout}

/-- A fully injective occurrence face supports every readout already defined
on that occurrence domain.  This is a derived fixed-domain result; it does
not admit a new source direction or mint U8 authority. -/
noncomputable def injectiveRangeFactor
    (injective : Function.Injective face)
    (read : Occurrence → AnyOutput) :
    Set.range face → AnyOutput :=
  read ∘ (Equiv.ofInjective face injective).symm

theorem injectiveRangeFactor_commutes
    (injective : Function.Injective face)
    (read : Occurrence → AnyOutput)
    (occurrence : Occurrence) :
    injectiveRangeFactor injective read
        ⟨face occurrence, occurrence, rfl⟩ =
      read occurrence := by
  change read ((Equiv.ofInjective face injective).symm
    ⟨face occurrence, occurrence, rfl⟩) = read occurrence
  rw [Equiv.ofInjective_symm_apply]

theorem injectiveRangeFactor_unique
    (injective : Function.Injective face)
    (read : Occurrence → AnyOutput)
    (candidate : Set.range face → AnyOutput)
    (commutes : ∀ occurrence,
      candidate ⟨face occurrence, occurrence, rfl⟩ = read occurrence) :
    candidate = injectiveRangeFactor injective read := by
  funext point
  rcases point.property with ⟨occurrence, occurrence_eq⟩
  have point_eq : point = ⟨face occurrence, occurrence, rfl⟩ :=
    Subtype.ext occurrence_eq.symm
  rw [point_eq, commutes occurrence,
    injectiveRangeFactor_commutes injective read occurrence]

theorem everyCurrentReadout_uniqueFactorization
    (injective : Function.Injective face)
    (read : Occurrence → AnyOutput) :
    ∃! factor : Set.range face → AnyOutput,
      ∀ occurrence,
        factor ⟨face occurrence, occurrence, rfl⟩ = read occurrence :=
  ⟨injectiveRangeFactor injective read,
    injectiveRangeFactor_commutes injective read,
    fun candidate commutes =>
      injectiveRangeFactor_unique injective read candidate commutes⟩

variable {Alternate : Type uAlternate}
variable {alternate : Occurrence → Alternate}

/-- Any second carrier with the same exact consumer kernel is canonically
equivalent to the first one over the same occurrences. -/
noncomputable def completeCarrierEquiv
    (exact : FaceKernelExactAt system face)
    (alternateExact : FaceKernelExactAt system alternate) :
    Set.range face ≃ Set.range alternate :=
  exact.quotientEquivRange.symm.trans alternateExact.quotientEquivRange

@[simp] theorem completeCarrierEquiv_commutes
    (exact : FaceKernelExactAt system face)
    (alternateExact : FaceKernelExactAt system alternate)
    (occurrence : Occurrence) :
    exact.completeCarrierEquiv alternateExact
        ⟨face occurrence, occurrence, rfl⟩ =
      ⟨alternate occurrence, occurrence, rfl⟩ := by
  rw [← exact.quotientEquivRange_mk occurrence,
    completeCarrierEquiv]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  exact alternateExact.quotientEquivRange_mk occurrence

/-- The commuting equivalence between complete carriers is unique. -/
theorem completeCarrierEquiv_unique
    (exact : FaceKernelExactAt system face)
    (alternateExact : FaceKernelExactAt system alternate)
    (candidate : Set.range face ≃ Set.range alternate)
    (commutes : ∀ occurrence,
      candidate ⟨face occurrence, occurrence, rfl⟩ =
        ⟨alternate occurrence, occurrence, rfl⟩) :
    candidate = exact.completeCarrierEquiv alternateExact := by
  apply Equiv.ext
  intro point
  rcases point.property with ⟨occurrence, occurrence_eq⟩
  have point_eq : point = ⟨face occurrence, occurrence, rfl⟩ :=
    Subtype.ext occurrence_eq.symm
  rw [point_eq, commutes occurrence,
    exact.completeCarrierEquiv_commutes alternateExact occurrence]

end FaceKernelExactAt

end Representation
end Consciousness
end NoIslandNoMagic
end SaturationMonoid
