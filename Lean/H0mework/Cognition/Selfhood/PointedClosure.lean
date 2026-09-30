import H0mework.Cognition.Selfhood.LivingClosure

/-!
# Pointed living-closure classification

An operational classifier identifies the observer/effect anchor with the
independent-consumer fibre of one source-generated witness.  Kernel stability
then classifies six-point closure by the canonical face without any occurrence
injectivity.  The strictly stronger occurrence equality is derived from the
weaker witness-local singleton-fibre law, not assumed globally.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Closure
namespace Canonical

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

universe uOccurrence uReadout uOutput uFace

/-- Source witness plus the exact bridge from the two operational closure
coordinates to its independent-consumer fibre.  No occurrence separation,
remaining closure coordinate, quotient theorem, or U8 receipt is stored. -/
structure OperationalLivingClassifierAt
    {Occurrence : Type uOccurrence}
    (system : IndependentConsumerSystem.{uOccurrence, uReadout} Occurrence)
    (closure : LivingClosureStructure Occurrence)
    (witness : Occurrence) : Prop where
  witnessClosure : SixPointLivingClosureAt closure witness
  anchorExact : ∀ occurrence,
    OperationalAnchorAt closure occurrence ↔
      system.Indistinguishable occurrence witness

/-- Any pointed predicate contained in a locally separated consumer fibre and
inhabited by its witness classifies that exact occurrence. -/
theorem pointedPredicate_iff_eq_witness
    {Occurrence : Type uOccurrence}
    {system : IndependentConsumerSystem.{uOccurrence, uReadout} Occurrence}
    {witness : Occurrence}
    (separated : WitnessSeparatedAt system witness)
    (predicate : Occurrence → Prop)
    (witnessProperty : predicate witness)
    (toWitnessFibre : ∀ {current}, predicate current →
      system.Indistinguishable current witness)
    (occurrence : Occurrence) :
    predicate occurrence ↔ occurrence = witness := by
  constructor
  · intro property
    exact separated (toWitnessFibre property)
  · intro occurrenceExact
    subst occurrence
    exact witnessProperty

namespace OperationalLivingClassifierAt

variable {Occurrence : Type uOccurrence}
variable {system : IndependentConsumerSystem.{uOccurrence, uReadout}
  Occurrence}
variable {closure : LivingClosureStructure Occurrence}
variable {witness occurrence : Occurrence}

theorem sixPoint_implies_indistinguishable
    (classifier : OperationalLivingClassifierAt system closure witness)
    (living : SixPointLivingClosureAt closure occurrence) :
    system.Indistinguishable occurrence witness :=
  (classifier.anchorExact occurrence).1 living.operationalAnchor

/-- Quotient-level crown: kernel-stable six-point closure is exactly the
consumer fibre of the source witness.  No occurrence injectivity is used. -/
theorem sixPoint_iff_indistinguishable_of_kernelStable
    (classifier : OperationalLivingClassifierAt system closure witness)
    (stable : LivingClosureKernelStableAtWitness system closure witness)
    (occurrence : Occurrence) :
    SixPointLivingClosureAt closure occurrence ↔
      system.Indistinguishable occurrence witness := by
  constructor
  · exact classifier.sixPoint_implies_indistinguishable
  · intro indistinguishable
    apply SixPointLivingClosureAt.ofHolds
    intro coordinate
    exact (stable coordinate indistinguishable).2
      (classifier.witnessClosure.holds coordinate)

theorem sixPoint_iff_canonicalRead_eq_of_kernelStable
    (classifier : OperationalLivingClassifierAt system closure witness)
    (stable : LivingClosureKernelStableAtWitness system closure witness)
    (occurrence : Occurrence) :
    SixPointLivingClosureAt closure occurrence ↔
      system.canonicalRead occurrence = system.canonicalRead witness :=
  (classifier.sixPoint_iff_indistinguishable_of_kernelStable stable occurrence
    ).trans
      (system.canonicalRead_eq_iff_indistinguishable occurrence witness).symm

/-- The pointed living fibre is representation-independent for every exact
complete face of the same consumer system. -/
theorem sixPoint_iff_completeFace_eq_of_kernelStable
    (classifier : OperationalLivingClassifierAt system closure witness)
    (stable : LivingClosureKernelStableAtWitness system closure witness)
    {Face : Type uFace} (face : Occurrence → Face)
    (exact : FaceKernelExactAt system face)
    (occurrence : Occurrence) :
    SixPointLivingClosureAt closure occurrence ↔
      face occurrence = face witness :=
  (classifier.sixPoint_iff_indistinguishable_of_kernelStable stable occurrence
    ).trans (exact occurrence witness).symm

/-- Occurrence-level crown.  Witness-local separation is strictly weaker than
global injectivity of the canonical face. -/
theorem sixPoint_iff_eq_witness
    (classifier : OperationalLivingClassifierAt system closure witness)
    (separated : WitnessSeparatedAt system witness)
    (occurrence : Occurrence) :
    SixPointLivingClosureAt closure occurrence ↔ occurrence = witness :=
  pointedPredicate_iff_eq_witness separated
    (SixPointLivingClosureAt closure) classifier.witnessClosure
    classifier.sixPoint_implies_indistinguishable occurrence

theorem sixPoint_iff_indistinguishable_of_witnessSeparated
    (classifier : OperationalLivingClassifierAt system closure witness)
    (separated : WitnessSeparatedAt system witness)
    (occurrence : Occurrence) :
    SixPointLivingClosureAt closure occurrence ↔
      system.Indistinguishable occurrence witness := by
  rw [classifier.sixPoint_iff_eq_witness separated occurrence]
  constructor
  · intro occurrenceExact
    subst occurrence
    exact system.indistinguishable_refl witness
  · exact separated

theorem operationalAnchor_iff_eq_witness
    (classifier : OperationalLivingClassifierAt system closure witness)
    (separated : WitnessSeparatedAt system witness)
    (occurrence : Occurrence) :
    OperationalAnchorAt closure occurrence ↔ occurrence = witness := by
  rw [classifier.anchorExact occurrence]
  constructor
  · exact separated
  · intro occurrenceExact
    subst occurrence
    exact system.indistinguishable_refl witness

theorem sixPoint_set_eq_canonicalFibre_of_kernelStable
    (classifier : OperationalLivingClassifierAt system closure witness)
    (stable : LivingClosureKernelStableAtWitness system closure witness) :
    {current | SixPointLivingClosureAt closure current} =
      {current |
        system.canonicalRead current = system.canonicalRead witness} := by
  ext current
  exact classifier.sixPoint_iff_canonicalRead_eq_of_kernelStable stable current

theorem sixPoint_set_eq_singleton_of_witnessSeparated
    (classifier : OperationalLivingClassifierAt system closure witness)
    (separated : WitnessSeparatedAt system witness) :
    {current | SixPointLivingClosureAt closure current} = {witness} := by
  ext current
  exact classifier.sixPoint_iff_eq_witness separated current

/-- Every two live occurrences belong to one operational consumer class even
when that class contains more than one occurrence. -/
theorem sixPointOccurrences_indistinguishable
    (classifier : OperationalLivingClassifierAt system closure witness)
    {left right : Occurrence}
    (leftLiving : SixPointLivingClosureAt closure left)
    (rightLiving : SixPointLivingClosureAt closure right) :
    system.Indistinguishable left right :=
  system.indistinguishable_trans
    (classifier.sixPoint_implies_indistinguishable leftLiving)
    (system.indistinguishable_symm
      (classifier.sixPoint_implies_indistinguishable rightLiving))

theorem compatibleReadout_constantOnSixPoint
    (classifier : OperationalLivingClassifierAt system closure witness)
    {Output : Type uOutput} (readout : Occurrence → Output)
    (compatible : system.ReadoutCompatible readout)
    {left right : Occurrence}
    (leftLiving : SixPointLivingClosureAt closure left)
    (rightLiving : SixPointLivingClosureAt closure right) :
    readout left = readout right :=
  compatible
    (classifier.sixPointOccurrences_indistinguishable leftLiving rightLiving)

/-- A new readout that splits two six-point occurrences is a concrete escape
from the old canonical kernel.  This generates the existing mathematical
revision target but does not mint source/U8 authority. -/
theorem splittingReadout_generatesKernelEscape
    (classifier : OperationalLivingClassifierAt system closure witness)
    (newReadout : IndependentReadout.{uOccurrence, uReadout} Occurrence)
    {left right : Occurrence}
    (leftLiving : SixPointLivingClosureAt closure left)
    (rightLiving : SixPointLivingClosureAt closure right)
    (different : newReadout.read left ≠ newReadout.read right) :
    FaceKernelEscapeAt system.canonicalRead newReadout := by
  exact ⟨left, right,
    (system.canonicalKernelExact left right).2
      (classifier.sixPointOccurrences_indistinguishable leftLiving rightLiving),
    different⟩

end OperationalLivingClassifierAt

end Canonical
end Closure
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Canonical.OperationalLivingClassifierAt.sixPoint_iff_canonicalRead_eq_of_kernelStable
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Canonical.OperationalLivingClassifierAt.sixPoint_iff_eq_witness
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Canonical.OperationalLivingClassifierAt.sixPoint_iff_completeFace_eq_of_kernelStable
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Canonical.OperationalLivingClassifierAt.splittingReadout_generatesKernelEscape
