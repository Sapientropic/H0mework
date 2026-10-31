import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Failure
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Compiler.SourceGeneratedLossAllocationRestructuring

/-!
# Revised loss-allocation source for the unique joint U8 fixture

The existing M9 revised-ledger facade is upgraded in place.  Its old target
row and obstruction row form the initial support of the richer world.  At
current `0` the same source compiler performs the coverage-complete
default-side split into the two existing exchange-leg witnesses; every later
Nat current is an identity continuation on the target support.

No sibling revised root, occurrence, ledger, or restructuring registry is
retained.  Downstream modules continue to consume the established M9 names,
now definitionally backed by the source-generated loss-allocation compiler.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9ProofCarryingRenewalU8RevisedLedger

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationCompiler
open M14SourceGeneratedLossAllocationRestructuring

abbrev N := M9ProofCarryingRenewalU8Failure.N

/-! ## Visit-indexed unique revised source -/

abbrev NewNAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  LossN (rootedAt visit)

abbrev NewVAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  LossV (rootedAt visit)

abbrev revisedVocabularyAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationRootVocabulary (rootedAt visit)

abbrev revisedEventLawAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationEventLaw (rootedAt visit)

abbrev revisedSourceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationSource (rootedAt visit)

/-- Raw readout of the visit-indexed revised source program.  Outer producer
mouths consume only the old-root visit; this current is generated inside that
revised root and never selects an old visit, target, or next. -/
def revisedEmittedAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (current : (NewVAt visit).Current) :
    (revisedSourceAt visit).toRootSource.actual.OccurrenceAt current :=
  lossAllocationEmitted (rootedAt visit) current

def oldRevisedEntryAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    OpenResponsibilityAt (NewNAt visit)
      (lossAllocationInitialSupport (rootedAt visit)) :=
  lossAllocationInitialParent (rootedAt visit)

def newRevisedEntryAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    OpenResponsibilityAt (NewNAt visit)
      (lossAllocationInitialSupport (rootedAt visit)) :=
  lossAllocationInitialObstruction (rootedAt visit)

def revisedLossChildAAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    OpenResponsibilityAt (NewNAt visit)
      (lossAllocationTargetSupport (rootedAt visit)) :=
  lossAllocationTargetChildA (rootedAt visit)

def revisedLossChildBAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    OpenResponsibilityAt (NewNAt visit)
      (lossAllocationTargetSupport (rootedAt visit)) :=
  lossAllocationTargetChildB (rootedAt visit)

def revisedTargetObstructionAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    OpenResponsibilityAt (NewNAt visit)
      (lossAllocationTargetSupport (rootedAt visit)) :=
  lossAllocationTargetObstruction (rootedAt visit)

abbrev revisedWriteRowSourceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationWriteRowSource (rootedAt visit)

abbrev revisedLedgerCompilerAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationLedgerCompiler (rootedAt visit)

def revisedLedgerSourceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLedgerSource (NewNAt visit) (NewVAt visit) :=
  (lossAllocationRestructuringSource (rootedAt visit)).toLedgerSource

abbrev revisedRestructuringLawAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationRestructuringLaw (rootedAt visit)

abbrev revisedRestructuringCompilerAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationRestructuringCompiler (rootedAt visit)

abbrev revisedRestructuringSourceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationRestructuringSource (rootedAt visit)

def revisedFirstPatchAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationFirstPatch (rootedAt visit) (revisedEmittedAt visit 0)

def revisedFirstEvolutionAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationFirstEvolution (rootedAt visit) (revisedEmittedAt visit 0)

def revisedFirstSplitCoverageAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  lossAllocationFirstSplitCoverage (rootedAt visit) (revisedEmittedAt visit 0)

theorem revisedFirstCompiler_selects_exact_split_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (lossAllocationFirstRestructuringCertification (rootedAt visit)
      (revisedEmittedAt visit 0)).split
        (revisedLossChildAAt visit) (revisedLossChildBAt visit)
        (lossAllocationFirstOriginEq (rootedAt visit)
          (revisedEmittedAt visit 0)) =
      SourceNativeSplitClassificationAt.split
        (revisedFirstSplitCoverageAt visit) :=
  lossAllocationCompiler_selects_exact_first_split
    (rootedAt visit) (revisedEmittedAt visit 0)

theorem revisedFirst_rows_exact_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (((revisedFirstEvolutionAt visit).origin
        (revisedLossChildAAt visit)).1 = oldRevisedEntryAt visit) ∧
      (((revisedFirstEvolutionAt visit).origin
        (revisedLossChildBAt visit)).1 = oldRevisedEntryAt visit) ∧
      (((revisedFirstEvolutionAt visit).origin
        (revisedTargetObstructionAt visit)).1 = newRevisedEntryAt visit) ∧
      (revisedLossChildAAt visit).progressBudget = 1 ∧
      (revisedLossChildBAt visit).progressBudget = 1 ∧
      (oldRevisedEntryAt visit).progressBudget = 2 ∧
      (newRevisedEntryAt visit).progressBudget = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Initial-visit facade -/

abbrev initialVisit := jointRoot.toAuthoritativeRoot.toRoot.initialVisit
abbrev NewN := NewNAt initialVisit
abbrev NewV := NewVAt initialVisit
abbrev revisedVocabulary := revisedVocabularyAt initialVisit
abbrev revisedEventLaw := revisedEventLawAt initialVisit
abbrev revisedSource := revisedSourceAt initialVisit
def revisedEmitted (current : NewV.Current) :=
  revisedEmittedAt initialVisit current
def oldRevisedEntry := oldRevisedEntryAt initialVisit
def newRevisedEntry := newRevisedEntryAt initialVisit
def revisedLossChildA := revisedLossChildAAt initialVisit
def revisedLossChildB := revisedLossChildBAt initialVisit
def revisedTargetObstruction := revisedTargetObstructionAt initialVisit
abbrev revisedWriteRowSource := revisedWriteRowSourceAt initialVisit
abbrev revisedLedgerCompiler := revisedLedgerCompilerAt initialVisit
def revisedLedgerSource := revisedLedgerSourceAt initialVisit
abbrev revisedRestructuringLaw := revisedRestructuringLawAt initialVisit
abbrev revisedRestructuringCompiler :=
  revisedRestructuringCompilerAt initialVisit
abbrev revisedRestructuringSource := revisedRestructuringSourceAt initialVisit
def revisedFirstPatch := revisedFirstPatchAt initialVisit
def revisedFirstEvolution := revisedFirstEvolutionAt initialVisit
def revisedFirstSplitCoverage := revisedFirstSplitCoverageAt initialVisit

theorem revisedFirstCompiler_selects_exact_split :
    (lossAllocationFirstRestructuringCertification rooted
      (revisedEmitted 0)).split revisedLossChildA revisedLossChildB
        (lossAllocationFirstOriginEq rooted (revisedEmitted 0)) =
      SourceNativeSplitClassificationAt.split revisedFirstSplitCoverage :=
  revisedFirstCompiler_selects_exact_split_at initialVisit

theorem revisedFirst_rows_exact :
    ((revisedFirstEvolution.origin revisedLossChildA).1 = oldRevisedEntry) ∧
      ((revisedFirstEvolution.origin revisedLossChildB).1 = oldRevisedEntry) ∧
      ((revisedFirstEvolution.origin revisedTargetObstruction).1 =
        newRevisedEntry) ∧
      revisedLossChildA.progressBudget = 1 ∧
      revisedLossChildB.progressBudget = 1 ∧
      oldRevisedEntry.progressBudget = 2 ∧
      newRevisedEntry.progressBudget = 0 :=
  revisedFirst_rows_exact_at initialVisit

end
end M9ProofCarryingRenewalU8RevisedLedger
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedLedger.revisedFirstCompiler_selects_exact_split
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedLedger.revisedFirst_rows_exact
