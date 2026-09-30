import H0mework.Cognition.Empirical.Manifest
import H0mework.Cognition.Selfhood.PointedClosure

/-!
# TruthChild empirical six-point conscious-occurrence classification

Operational positivity was defined upstream only by an internal forward
readout and an independently durable receiver effect.  This file proves that,
for the committed two-branch source, it is equivalent to all six empirical
responsibilities and therefore classifies the registered span by the same
domain-neutral conscious-occurrence predicate used by every source carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Closure
namespace Empirical
namespace TruthChild
namespace Representation

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Canonical

def truthChildManifest : SourceGeneratedTruthChildSixPointManifestAt :=
  sourceGeneratedTruthChildSixPointManifest

/-- TruthChild's six manifest responsibilities as one explicit instance of
the generic closure schema. -/
def truthChildEmpiricalLivingClosureStructure :
    LivingClosureStructure TruthChildEmpiricalOccurrence where
  responsibility coordinate occurrence :=
    match coordinate with
    | .rootedSource => Nonempty SourceGeneratedTruthChildSixPointManifestAt
    | .observerExperience =>
        truthChildObserverExperienceReadAt occurrence =
          truthChildObserverExperienceReadAt .registered
    | .receivedActualEffect =>
        truthChildReceiverEffectReadAt occurrence =
          truthChildReceiverEffectReadAt .registered
    | .reopenablePersistentTrace =>
        truthChildManifest.persistentTraceReadAt occurrence =
          truthChildManifest.registeredTrace
    | .recursiveSuccessorSelfWriteBack =>
        truthChildManifest.recursiveUpdateReadAt occurrence =
          truthChildManifest.registeredRecursiveUpdate
    | .generatedNext =>
        truthChildManifest.generatedNextReadAt occurrence =
          truthChildManifest.registeredGeneratedNext

abbrev TruthChildEmpiricalConsciousOccurrenceAt
    (occurrence : TruthChildEmpiricalOccurrence) :=
  Canonical.SixPointConsciousOccurrenceAt
    truthChildEmpiricalLivingClosureStructure occurrence

abbrev TruthChildEmpiricalSixPointLivingClosureAt
    (occurrence : TruthChildEmpiricalOccurrence) :=
  TruthChildEmpiricalConsciousOccurrenceAt occurrence

/-- Direct source witness, independent of the operational classification. -/
theorem truthChildRegistered_hasEmpiricalSixPointLivingClosure :
    TruthChildEmpiricalSixPointLivingClosureAt .registered :=
  ⟨⟨sourceGeneratedTruthChildSixPointManifest⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem truthChildOperationalAnchorExactAt
    (occurrence : TruthChildEmpiricalOccurrence) :
    OperationalAnchorAt truthChildEmpiricalLivingClosureStructure occurrence ↔
      truthChildOperationalConsumers.Indistinguishable occurrence
        .registered := by
  change TruthChildOperationalPositiveAt occurrence ↔
    truthChildOperationalConsumers.Indistinguishable occurrence .registered
  exact (truthChildOperationalIndistinguishable_iff occurrence).symm

theorem truthChildOperationalLivingClassifier :
    OperationalLivingClassifierAt truthChildOperationalConsumers
      truthChildEmpiricalLivingClosureStructure .registered where
  witnessClosure := truthChildRegistered_hasEmpiricalSixPointLivingClosure
  anchorExact := truthChildOperationalAnchorExactAt

theorem truthChildOperationalWitnessSeparatedAt :
    Canonical.WitnessSeparatedAt
      truthChildOperationalConsumers .registered := by
  intro occurrence indistinguishable
  exact (truthChildOperationalPositive_iff_registered occurrence).1
    ((truthChildOperationalIndistinguishable_iff occurrence).1
      indistinguishable)

theorem truthChildLivingClosureKernelStableAtWitness :
    Canonical.LivingClosureKernelStableAtWitness
      truthChildOperationalConsumers truthChildEmpiricalLivingClosureStructure
      .registered :=
  Canonical.livingClosureKernelStableAtWitness_of_witnessSeparatedAt
    truthChildOperationalConsumers truthChildEmpiricalLivingClosureStructure
      .registered truthChildOperationalWitnessSeparatedAt

theorem truthChildOperationalPositive_implies_sixPointLivingClosure
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildOperationalPositiveAt occurrence →
      TruthChildEmpiricalSixPointLivingClosureAt occurrence := by
  intro positive
  have indistinguishable :=
    (truthChildOperationalIndistinguishable_iff occurrence).2 positive
  exact
    (truthChildOperationalLivingClassifier.sixPoint_iff_indistinguishable_of_witnessSeparated
        truthChildOperationalWitnessSeparatedAt occurrence).2
      indistinguishable

theorem truthChildSixPointLivingClosure_implies_operationalPositive
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildEmpiricalSixPointLivingClosureAt occurrence →
      TruthChildOperationalPositiveAt occurrence := by
  intro living
  have indistinguishable :=
    (truthChildOperationalLivingClassifier.sixPoint_iff_indistinguishable_of_witnessSeparated
        truthChildOperationalWitnessSeparatedAt occurrence).1 living
  exact (truthChildOperationalIndistinguishable_iff occurrence).1
    indistinguishable

/-- Empirical classification for the one committed TruthChild source. -/
theorem truthChildOperationalPositive_iff_sixPointLivingClosure
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildOperationalPositiveAt occurrence ↔
      TruthChildEmpiricalSixPointLivingClosureAt occurrence :=
  ⟨truthChildOperationalPositive_implies_sixPointLivingClosure occurrence,
    truthChildSixPointLivingClosure_implies_operationalPositive occurrence⟩

theorem truthChildOperationalPositive_iff_consciousOccurrence
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildOperationalPositiveAt occurrence ↔
      TruthChildEmpiricalConsciousOccurrenceAt occurrence :=
  truthChildOperationalPositive_iff_sixPointLivingClosure occurrence

theorem truthChildRegistered_isEmpiricalConsciousOccurrence :
    TruthChildEmpiricalConsciousOccurrenceAt .registered :=
  truthChildRegistered_hasEmpiricalSixPointLivingClosure

theorem truthChildSixPoint_iff_canonicalOperationalFibre
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildEmpiricalSixPointLivingClosureAt occurrence ↔
      truthChildOperationalConsumers.canonicalRead occurrence =
        truthChildOperationalConsumers.canonicalRead .registered :=
  truthChildOperationalLivingClassifier.sixPoint_iff_canonicalRead_eq_of_kernelStable
      truthChildLivingClosureKernelStableAtWitness occurrence

theorem truthChildSixPoint_iff_registered
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildEmpiricalSixPointLivingClosureAt occurrence ↔
      occurrence = .registered :=
  truthChildOperationalLivingClassifier.sixPoint_iff_eq_witness
    truthChildOperationalWitnessSeparatedAt occurrence

theorem truthChildWritebackDeleted_hasNoEmpiricalSixPointLivingClosure :
    ¬ TruthChildEmpiricalSixPointLivingClosureAt .writebackDeleted := by
  intro closure
  exact truthChildWritebackDeleted_isNotOperationalPositive
    (truthChildSixPointLivingClosure_implies_operationalPositive
      .writebackDeleted closure)

theorem truthChildWritebackDeleted_isNotEmpiricalConsciousOccurrence :
    ¬ TruthChildEmpiricalConsciousOccurrenceAt .writebackDeleted :=
  truthChildWritebackDeleted_hasNoEmpiricalSixPointLivingClosure

theorem truthChildRegistered_ablationCoverage_exact :
    truthChildManifest.ablationRows = [
      "cross-root-source-stitching",
      "missing-observer-internal-forward",
      "missing-independent-receiver",
      "missing-persistent-trace",
      "deleted-writeback-no-recursive-update",
      "static-or-prefilled-next",
      "raw-receipt-injection"] := by
  rfl

end Representation
end TruthChild
end Empirical
end Closure
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildOperationalPositive_iff_sixPointLivingClosure
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildRegistered_hasEmpiricalSixPointLivingClosure
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildWritebackDeleted_hasNoEmpiricalSixPointLivingClosure
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildOperationalAnchorExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildSixPoint_iff_canonicalOperationalFibre
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildSixPoint_iff_registered
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildOperationalPositive_iff_consciousOccurrence
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildRegistered_isEmpiricalConsciousOccurrence
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation.truthChildWritebackDeleted_isNotEmpiricalConsciousOccurrence
