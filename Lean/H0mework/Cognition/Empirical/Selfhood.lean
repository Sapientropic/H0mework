import H0mework.Cognition.Selfhood.Representation
import H0mework.Cognition.Empirical.Classification

/-!
# TruthChild empirical self and personality crown

The fixed registered/write-back-deleted runtime pair already supplies an
independent observer/effect consumer family and source-bound trace,
recursive-update and generated-next evidence.  This file shows that the
operational personality code and the empirical self face have the same exact
kernel on that committed occurrence domain.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Selfhood
namespace Empirical
namespace TruthChild
namespace Representation

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Selfhood.Canonical
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation

noncomputable section

/-- Source-generated empirical self readout.  It uses only evidence already
bound by the manifest and carries no classifier or future field. -/
structure TruthChildEmpiricalSelfFace where
  persistentTrace : TruthChildPersistentTraceEvidence
  recursiveUpdate : TruthChildRecursiveUpdateEvidence
  generatedNext : TruthChildGeneratedNextEvidence
  deriving DecidableEq, Repr

def truthChildEmpiricalSelfFaceReadAt
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildEmpiricalSelfFace where
  persistentTrace := truthChildManifest.persistentTraceReadAt occurrence
  recursiveUpdate := truthChildManifest.recursiveUpdateReadAt occurrence
  generatedNext := truthChildManifest.generatedNextReadAt occurrence

@[simp] theorem truthChildRegisteredSelfFace_authoritative :
    (truthChildEmpiricalSelfFaceReadAt .registered
      ).recursiveUpdate.authoritative = true :=
  rfl

@[simp] theorem truthChildDeletedSelfFace_authoritative :
    (truthChildEmpiricalSelfFaceReadAt .writebackDeleted
      ).recursiveUpdate.authoritative = false :=
  rfl

def truthChildEmpiricalSelfhoodStructure :
    LivingSelfhoodStructure TruthChildEmpiricalOccurrence
      TruthChildEmpiricalSelfFace where
  closure := truthChildEmpiricalLivingClosureStructure
  actorRead := truthChildEmpiricalSelfFaceReadAt

abbrev truthChildEmpiricalPersonalityConsumers :=
  truthChildOperationalConsumers

theorem truthChildEmpiricalSelfFaceRead_injective :
    Function.Injective truthChildEmpiricalSelfFaceReadAt := by
  intro left right sameSelf
  cases left <;> cases right
  · rfl
  · have authorityEqual := congrArg
      (fun face => face.recursiveUpdate.authoritative) sameSelf
    simp at authorityEqual
  · have authorityEqual := congrArg
      (fun face => face.recursiveUpdate.authoritative) sameSelf
    simp at authorityEqual
  · rfl

theorem truthChildEmpiricalPersonalityDeterminesSelf :
    PersonalityDeterminesSelf truthChildEmpiricalPersonalityConsumers
      truthChildEmpiricalSelfhoodStructure := by
  intro left right samePersonality
  apply congrArg truthChildEmpiricalSelfFaceReadAt
  cases left <;> cases right
  · rfl
  · have deletedIndistinguishable :
        truthChildOperationalConsumers.Indistinguishable
          .writebackDeleted .registered :=
      truthChildOperationalConsumers.indistinguishable_symm samePersonality
    have impossible :
        TruthChildEmpiricalOccurrence.writebackDeleted = .registered :=
      (truthChildOperationalPositive_iff_registered .writebackDeleted).1
        ((truthChildOperationalIndistinguishable_iff .writebackDeleted).1
          deletedIndistinguishable)
    cases impossible
  · have impossible :
        TruthChildEmpiricalOccurrence.writebackDeleted = .registered :=
      (truthChildOperationalPositive_iff_registered .writebackDeleted).1
        ((truthChildOperationalIndistinguishable_iff .writebackDeleted).1
          samePersonality)
    cases impossible
  · rfl

theorem truthChildEmpiricalPersonalityStableWithinSelf :
    PersonalityStableWithinSelf truthChildEmpiricalPersonalityConsumers
      truthChildEmpiricalSelfhoodStructure := by
  intro left right sameSelf
  have sameOccurrence := truthChildEmpiricalSelfFaceRead_injective sameSelf
  subst right
  exact truthChildEmpiricalPersonalityConsumers.indistinguishable_refl left

theorem truthChildEmpiricalSelfPersonalityKernelExact :
    SelfPersonalityKernelExact truthChildEmpiricalPersonalityConsumers
      truthChildEmpiricalSelfhoodStructure :=
  (selfPersonalityKernelExact_iff truthChildEmpiricalPersonalityConsumers
    truthChildEmpiricalSelfhoodStructure).2
      ⟨truthChildEmpiricalPersonalityDeterminesSelf,
        truthChildEmpiricalPersonalityStableWithinSelf⟩

theorem truthChildRegistered_isEmpiricalLivingSelf :
    truthChildEmpiricalSelfhoodStructure.SelfAt .registered :=
  truthChildRegistered_hasEmpiricalSixPointLivingClosure

theorem truthChildWritebackDeleted_isNotEmpiricalLivingSelf :
    ¬ truthChildEmpiricalSelfhoodStructure.SelfAt .writebackDeleted :=
  truthChildWritebackDeleted_hasNoEmpiricalSixPointLivingClosure

theorem truthChildRegistered_deleted_differentSelf :
    truthChildEmpiricalSelfhoodStructure.DifferentSelfAt
      .registered .writebackDeleted := by
  intro sameSelf
  exact (by decide : TruthChildEmpiricalOccurrence.registered ≠
    .writebackDeleted) (truthChildEmpiricalSelfFaceRead_injective sameSelf)

theorem truthChildRegistered_deleted_differentPersonality :
    DifferentPersonalityAt truthChildEmpiricalPersonalityConsumers
      .registered .writebackDeleted := by
  intro samePersonality
  have deletedPositive : TruthChildOperationalPositiveAt .writebackDeleted :=
    (truthChildOperationalIndistinguishable_iff .writebackDeleted).1
      (truthChildEmpiricalPersonalityConsumers.indistinguishable_symm
        samePersonality)
  exact truthChildWritebackDeleted_isNotOperationalPositive deletedPositive

noncomputable def truthChildCanonicalSelfPersonalityCrown :
    CanonicalSelfPersonalityCrown
      truthChildEmpiricalPersonalityConsumers
      truthChildEmpiricalSelfhoodStructure :=
  canonicalSelfPersonalityCrown truthChildEmpiricalPersonalityConsumers
    truthChildEmpiricalSelfhoodStructure

theorem truthChildSelfReadout_uniqueFactorizationThroughPersonality :
    ∃! factor :
        PersonalityCarrier truthChildEmpiricalPersonalityConsumers →
          TruthChildEmpiricalSelfFace,
      ∀ occurrence,
        factor
            ⟨truthChildEmpiricalPersonalityConsumers.canonicalRead occurrence,
              occurrence, rfl⟩ =
          truthChildEmpiricalSelfFaceReadAt occurrence :=
  ((personalityDeterminesSelf_iff_uniqueFactorization
    truthChildEmpiricalPersonalityConsumers
    truthChildEmpiricalSelfhoodStructure).1
      truthChildEmpiricalPersonalityDeterminesSelf)

structure TruthChildEmpiricalSelfPersonalityCrownAt : Prop where
  registeredLivingSelf :
    truthChildEmpiricalSelfhoodStructure.SelfAt .registered
  deletedNotLivingSelf :
    ¬ truthChildEmpiricalSelfhoodStructure.SelfAt .writebackDeleted
  kernelExact :
    SelfPersonalityKernelExact truthChildEmpiricalPersonalityConsumers
      truthChildEmpiricalSelfhoodStructure
  deletionChangesSelf :
    truthChildEmpiricalSelfhoodStructure.DifferentSelfAt
      .registered .writebackDeleted
  deletionChangesPersonality :
    DifferentPersonalityAt truthChildEmpiricalPersonalityConsumers
      .registered .writebackDeleted
  canonicalCrown : Nonempty
    (CanonicalSelfPersonalityCrown
      truthChildEmpiricalPersonalityConsumers
      truthChildEmpiricalSelfhoodStructure)
  selfFactorization : type_of%
    truthChildSelfReadout_uniqueFactorizationThroughPersonality
  consciousOccurrence :
    TruthChildEmpiricalConsciousOccurrenceAt .registered
  ablationCoverage : truthChildManifest.ablationRows = [
    "cross-root-source-stitching",
    "missing-observer-internal-forward",
    "missing-independent-receiver",
    "missing-persistent-trace",
    "deleted-writeback-no-recursive-update",
    "static-or-prefilled-next",
    "raw-receipt-injection"]

theorem truthChildEmpiricalSelfPersonalityCrown :
    TruthChildEmpiricalSelfPersonalityCrownAt where
  registeredLivingSelf := truthChildRegistered_isEmpiricalLivingSelf
  deletedNotLivingSelf := truthChildWritebackDeleted_isNotEmpiricalLivingSelf
  kernelExact := truthChildEmpiricalSelfPersonalityKernelExact
  deletionChangesSelf := truthChildRegistered_deleted_differentSelf
  deletionChangesPersonality :=
    truthChildRegistered_deleted_differentPersonality
  canonicalCrown := ⟨truthChildCanonicalSelfPersonalityCrown⟩
  selfFactorization := truthChildSelfReadout_uniqueFactorizationThroughPersonality
  consciousOccurrence := truthChildRegistered_isEmpiricalConsciousOccurrence
  ablationCoverage := truthChildRegistered_ablationCoverage_exact

theorem truthChildEmpiricalSelfPersonalityCrown_directConsumer :
    Nonempty TruthChildEmpiricalSelfPersonalityCrownAt ∧
      type_of% truthChildRegistered_isEmpiricalLivingSelf ∧
      type_of% truthChildWritebackDeleted_isNotEmpiricalLivingSelf ∧
      type_of% truthChildEmpiricalSelfPersonalityKernelExact ∧
      type_of% truthChildRegistered_deleted_differentSelf ∧
      type_of% truthChildRegistered_deleted_differentPersonality ∧
      type_of% truthChildSelfReadout_uniqueFactorizationThroughPersonality :=
  ⟨⟨truthChildEmpiricalSelfPersonalityCrown⟩,
    truthChildRegistered_isEmpiricalLivingSelf,
    truthChildWritebackDeleted_isNotEmpiricalLivingSelf,
    truthChildEmpiricalSelfPersonalityKernelExact,
    truthChildRegistered_deleted_differentSelf,
    truthChildRegistered_deleted_differentPersonality,
    truthChildSelfReadout_uniqueFactorizationThroughPersonality⟩

end
end Representation
end TruthChild
end Empirical
end Selfhood
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Selfhood.Empirical.TruthChild.Representation.truthChildEmpiricalSelfPersonalityCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Selfhood.Empirical.TruthChild.Representation.truthChildEmpiricalSelfPersonalityCrown_directConsumer
