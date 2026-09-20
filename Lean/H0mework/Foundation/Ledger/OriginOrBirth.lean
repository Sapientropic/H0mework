import H0mework.Foundation.Source.Root

/-!
# Source-generated target origin or birth provenance

An ordinary whole-ledger write already carries a total compiler-selected
origin for every target entry.  This kernel exposes that canonical old origin
and proves that the same row cannot be relabelled as fresh birth.  Genuine
birth remains a separate source-generated admission occurrence; this file
does not install an `old | birth` choice, registry or closed future ontology.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Exact old debt origin of one target entry in a complete source ledger. -/
abbrev ExactTargetDebtOriginAt
    {N : WorldRelationNetwork.{u}}
    (source : CompleteLiveLedgerAt N)
    {targetSupport : N.Support}
    (targetEntry : OpenResponsibilityAt N targetSupport) : Type u :=
  Sigma fun sourceEntry : source.Entry =>
    RootDebtLineageAt N sourceEntry targetEntry

/-- Any exact old origin constructively excludes the fresh branch. -/
def ExactTargetDebtOriginAt.excludesFresh
    {N : WorldRelationNetwork.{u}}
    {source : CompleteLiveLedgerAt N}
    {targetSupport : N.Support}
    {targetEntry : OpenResponsibilityAt N targetSupport}
    (origin : ExactTargetDebtOriginAt source targetEntry)
    (fresh : RootDebtFreshAt N source.support targetEntry) : PEmpty :=
  fresh.excludesPrior origin.1 origin.2

namespace LedgerWriteEvolutionAt

/-- A continuing whole-ledger write always produces one canonical old origin. -/
def targetOldOrigin
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N source target)
    (targetEntry : target.Entry) :
    ExactTargetDebtOriginAt source targetEntry :=
  ⟨(evolution.origin targetEntry).1,
    (evolution.origin targetEntry).2.toDebtLineage⟩

def excludesTargetFresh
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N source target)
    (targetEntry : target.Entry)
    (fresh : RootDebtFreshAt N source.support targetEntry) : PEmpty :=
  (evolution.targetOldOrigin targetEntry).excludesFresh fresh

end LedgerWriteEvolutionAt

/-- Zero-field provenance seal for one compiler-selected ordinary target. -/
structure ExactTargetOldOriginProvenanceAt
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N source target)
    (targetEntry : target.Entry) : Type u where
  private mk ::

def LedgerWriteEvolutionAt.exactTargetOldOriginProvenanceAt
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N source target)
    (targetEntry : target.Entry) :
    ExactTargetOldOriginProvenanceAt evolution targetEntry :=
  ⟨⟩

namespace ExactTargetOldOriginProvenanceAt

instance instSubsingleton
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N source target}
    {targetEntry : target.Entry} :
    Subsingleton (ExactTargetOldOriginProvenanceAt evolution targetEntry) :=
  ⟨fun left right => by cases left; cases right; rfl⟩

def oldOrigin
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N source target}
    {targetEntry : target.Entry}
    (_provenance : ExactTargetOldOriginProvenanceAt evolution targetEntry) :
    source.Entry :=
  (evolution.origin targetEntry).1

def oldEvolution
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N source target}
    {targetEntry : target.Entry}
    (provenance : ExactTargetOldOriginProvenanceAt evolution targetEntry) :
    LedgerEntryEvolutionAt N provenance.oldOrigin targetEntry :=
  (evolution.origin targetEntry).2

def oldDebtLineage
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N source target}
    {targetEntry : target.Entry}
    (provenance : ExactTargetOldOriginProvenanceAt evolution targetEntry) :
    RootDebtLineageAt N provenance.oldOrigin targetEntry :=
  provenance.oldEvolution.toDebtLineage

theorem progressBudget_not_refilled
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N source target}
    {targetEntry : target.Entry}
    (provenance : ExactTargetOldOriginProvenanceAt evolution targetEntry) :
    targetEntry.progressBudget <= provenance.oldOrigin.progressBudget :=
  provenance.oldEvolution.progressBudget_not_refilled

def excludesBirthFreshness
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N source target}
    {targetEntry : target.Entry}
    (provenance : ExactTargetOldOriginProvenanceAt evolution targetEntry)
    (fresh : RootDebtFreshAt N source.support targetEntry) : PEmpty :=
  fresh.excludesPrior provenance.oldOrigin provenance.oldDebtLineage

end ExactTargetOldOriginProvenanceAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ExactTargetDebtOriginAt.excludesFresh
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LedgerWriteEvolutionAt.targetOldOrigin
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LedgerWriteEvolutionAt.excludesTargetFresh
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ExactTargetOldOriginProvenanceAt.excludesBirthFreshness
