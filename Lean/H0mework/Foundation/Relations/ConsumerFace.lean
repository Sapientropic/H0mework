import H0mework.Foundation.Relations.ConsumerQuotient

/-!
# Canonical all-consumer dependent face

Every independently registered heterogeneous consumer contributes its own
coordinate.  Their dependent tuple is therefore a canonical face fixed by the
consumer system itself; callers supply neither a candidate carrier nor a
kernel/completeness certificate.

The authoritative carrier is `Set.range canonicalRead`, not the unrestricted
dependent function space.  Concrete source faces remain separate and compare
to this range only after their own source-generated exact-kernel theorem has
been proved.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Representation

universe uOccurrence uReadout uOutput uAlternate

namespace IndependentConsumerSystem

variable {Occurrence : Type uOccurrence}
variable (system : IndependentConsumerSystem.{uOccurrence, uReadout}
  Occurrence)

/-- The heterogeneous tuple of every independently registered output. -/
abbrev CanonicalFace :=
  (consumer : system.Consumer) → system.Output consumer

/-- The all-consumer face of one occurrence.  No concrete source carrier or
completeness witness is accepted as input. -/
def canonicalRead (occurrence : Occurrence) : system.CanonicalFace :=
  fun consumer => system.read consumer occurrence

@[simp] theorem canonicalRead_apply (occurrence : Occurrence)
    (consumer : system.Consumer) :
    system.canonicalRead occurrence consumer =
      system.read consumer occurrence :=
  rfl

/-- Equality of the dependent all-consumer tuple is exactly consumer
indistinguishability.  Both directions follow from the independent reads. -/
theorem canonicalKernelExact :
    FaceKernelExactAt system system.canonicalRead := by
  intro left right
  constructor
  · intro sameFace consumer
    exact congrFun sameFace consumer
  · intro sameConsumers
    funext consumer
    exact sameConsumers consumer

@[simp] theorem canonicalRead_eq_iff_indistinguishable
    (left right : Occurrence) :
    system.canonicalRead left = system.canonicalRead right ↔
      system.Indistinguishable left right :=
  system.canonicalKernelExact left right

/-- First-isomorphism realization of the independent-consumer quotient. -/
noncomputable def canonicalQuotientEquivRange :
    system.Quotient ≃ Set.range system.canonicalRead :=
  system.canonicalKernelExact.quotientEquivRange

@[simp] theorem canonicalQuotientEquivRange_mk
    (occurrence : Occurrence) :
    system.canonicalQuotientEquivRange
        (Quotient.mk system.setoid occurrence) =
      ⟨system.canonicalRead occurrence, occurrence, rfl⟩ :=
  system.canonicalKernelExact.quotientEquivRange_mk occurrence

/-- Every registered consumer has one unique coordinate readout on the
canonical range. -/
theorem everyConsumer_uniqueFactorization
    (consumer : system.Consumer) :
    ∃! factor : Set.range system.canonicalRead → system.Output consumer,
      ∀ occurrence,
        factor ⟨system.canonicalRead occurrence, occurrence, rfl⟩ =
          system.read consumer occurrence :=
  system.canonicalKernelExact.everyConsumer_unique_factorization consumer

/-- Exact condition for a further fixed-domain readout to descend to the
consumer quotient.  It says precisely that the readout introduces no new
distinction beyond the registered consumer kernel. -/
def ReadoutCompatible
    {Output : Type uOutput} (readout : Occurrence → Output) : Prop :=
  ∀ {left right : Occurrence},
    system.Indistinguishable left right →
      readout left = readout right

def compatibleQuotientRead
    {Output : Type uOutput} {readout : Occurrence → Output}
    (compatible : system.ReadoutCompatible readout) :
    system.Quotient → Output :=
  Quotient.lift readout (fun _left _right same => compatible same)

noncomputable def compatibleRangeFactor
    {Output : Type uOutput} {readout : Occurrence → Output}
    (compatible : system.ReadoutCompatible readout) :
    Set.range system.canonicalRead → Output :=
  system.compatibleQuotientRead compatible ∘
    system.canonicalQuotientEquivRange.symm

theorem compatibleRangeFactor_commutes
    {Output : Type uOutput} {readout : Occurrence → Output}
    (compatible : system.ReadoutCompatible readout)
    (occurrence : Occurrence) :
    system.compatibleRangeFactor compatible
        ⟨system.canonicalRead occurrence, occurrence, rfl⟩ =
      readout occurrence := by
  change system.compatibleQuotientRead compatible
      (system.canonicalQuotientEquivRange.symm
        ⟨system.canonicalRead occurrence, occurrence, rfl⟩) = _
  rw [← system.canonicalQuotientEquivRange_mk occurrence]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem compatibleRangeFactor_unique
    {Output : Type uOutput} {readout : Occurrence → Output}
    (compatible : system.ReadoutCompatible readout)
    (candidate : Set.range system.canonicalRead → Output)
    (commutes : ∀ occurrence,
      candidate ⟨system.canonicalRead occurrence, occurrence, rfl⟩ =
        readout occurrence) :
    candidate = system.compatibleRangeFactor compatible := by
  funext point
  rcases point.property with ⟨occurrence, occurrence_eq⟩
  have point_eq :
      point = ⟨system.canonicalRead occurrence, occurrence, rfl⟩ :=
    Subtype.ext occurrence_eq.symm
  rw [point_eq, commutes occurrence,
    system.compatibleRangeFactor_commutes compatible occurrence]

/-- A readout has a unique factorization through the canonical range iff it
respects exactly the registered consumer kernel. -/
theorem readoutCompatible_iff_uniqueFactorization
    {Output : Type uOutput} (readout : Occurrence → Output) :
    system.ReadoutCompatible readout ↔
      ∃! factor : Set.range system.canonicalRead → Output,
        ∀ occurrence,
          factor ⟨system.canonicalRead occurrence, occurrence, rfl⟩ =
            readout occurrence := by
  constructor
  · intro compatible
    exact ⟨system.compatibleRangeFactor compatible,
      system.compatibleRangeFactor_commutes compatible,
      fun candidate commutes =>
        system.compatibleRangeFactor_unique compatible candidate commutes⟩
  · rintro ⟨factor, commutes, _unique⟩ left right sameConsumers
    have sameFace :
        system.canonicalRead left = system.canonicalRead right :=
      (system.canonicalKernelExact left right).2 sameConsumers
    calc
      readout left =
          factor ⟨system.canonicalRead left, left, rfl⟩ :=
        (commutes left).symm
      _ = factor ⟨system.canonicalRead right, right, rfl⟩ := by
        congr 1
        exact Subtype.ext sameFace
      _ = readout right := commutes right

theorem canonicalRead_injective_iff_consumersSeparate :
    Function.Injective system.canonicalRead ↔
      ∀ {left right : Occurrence},
        system.Indistinguishable left right → left = right := by
  constructor
  · intro injective left right sameConsumers
    exact injective ((system.canonicalKernelExact left right).2 sameConsumers)
  · intro separates left right sameFace
    exact separates ((system.canonicalKernelExact left right).1 sameFace)

/-- If the registered consumers separate occurrences, every readout on that
fixed occurrence domain factors uniquely through the canonical range. -/
theorem everyFixedDomainReadout_uniqueFactorization
    (injective : Function.Injective system.canonicalRead)
    {Output : Type uOutput} (readout : Occurrence → Output) :
    ∃! factor : Set.range system.canonicalRead → Output,
      ∀ occurrence,
        factor ⟨system.canonicalRead occurrence, occurrence, rfl⟩ =
          readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization injective readout

/-- Every alternate exact complete carrier on this same occurrence domain is
uniquely commuting-isomorphic to the canonical consumer range. -/
theorem completeCarrier_uniqueIso
    {Alternate : Type uAlternate} (alternate : Occurrence → Alternate)
    (alternateExact : FaceKernelExactAt system alternate) :
    ∃! equivalence : Set.range system.canonicalRead ≃ Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨system.canonicalRead occurrence, occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ :=
  ⟨system.canonicalKernelExact.completeCarrierEquiv alternateExact,
    system.canonicalKernelExact.completeCarrierEquiv_commutes alternateExact,
    fun candidate commutes =>
      system.canonicalKernelExact.completeCarrierEquiv_unique alternateExact
        candidate commutes⟩

/-- A difference in the canonical tuple cannot remain invisible to every
registered consumer. -/
theorem noHiddenDirection
    {left right : Occurrence}
    (different : system.canonicalRead left ≠ system.canonicalRead right) :
    ¬ system.Indistinguishable left right :=
  system.canonicalKernelExact.noHiddenDirection different

end IndependentConsumerSystem

end Representation
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.IndependentConsumerSystem.canonicalKernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.IndependentConsumerSystem.canonicalQuotientEquivRange
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.IndependentConsumerSystem.readoutCompatible_iff_uniqueFactorization
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.IndependentConsumerSystem.completeCarrier_uniqueIso
