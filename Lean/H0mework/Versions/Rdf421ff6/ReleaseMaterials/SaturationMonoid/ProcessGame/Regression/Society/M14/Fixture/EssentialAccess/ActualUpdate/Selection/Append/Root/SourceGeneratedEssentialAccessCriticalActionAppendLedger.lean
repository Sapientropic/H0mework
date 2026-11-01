import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedEssentialAccessCriticalActionCarrier
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Root.Generic.SourceGeneratedRootedAccountedUnfoldingAppendLedger

/-!
# Essential-access wrapper of the polymorphic append ledger

The domain layer supplies only the carrier-generated relation seed.  Every
vocabulary, row, patch, compiler, restructuring and successor below is a thin
wrapper of the unique polymorphic rooted-accounted-unfolding append core.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalActionAppendLedger

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger

abbrev appendNextAtom
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  actionCarrier.action.criticalBearer.bearerLineage.seed

abbrev appendedCriticalSelectionCurrent
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  RootedAccountedUnfolding.occur (appendNextAtom actionCarrier)
    (AccountedBranches.singleton prior)

@[simp] theorem appendedCriticalSelectionCurrent_eq_generic
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    appendedCriticalSelectionCurrent prior actionCarrier =
      rootedAppendedCurrent prior (appendNextAtom actionCarrier) :=
  rfl

abbrev appendNativeTarget
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    (current : EssentialAccessCriticalSelectionCurrent) :=
  rootedAppendNativeTarget prior (appendNextAtom actionCarrier) current

theorem appendedCriticalSelectionCurrent_ne_prior
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    appendedCriticalSelectionCurrent prior actionCarrier ≠ prior :=
  rootedAppendedCurrent_ne_prior prior (appendNextAtom actionCarrier)

@[simp] theorem appendNativeTarget_initial
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    appendNativeTarget prior actionCarrier prior =
      appendedCriticalSelectionCurrent prior actionCarrier :=
  rootedAppendNativeTarget_initial prior (appendNextAtom actionCarrier)

@[simp] theorem appendNativeTarget_after_append
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    appendNativeTarget prior actionCarrier
        (appendedCriticalSelectionCurrent prior actionCarrier) =
      retainedSelectionNext
        (appendedCriticalSelectionCurrent prior actionCarrier) :=
  rootedAppendNativeTarget_after_append prior (appendNextAtom actionCarrier)

abbrev appendVocabulary
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendVocabulary prior (appendNextAtom actionCarrier)

abbrev AppendVAt
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  RootedAppendVAt prior (appendNextAtom actionCarrier)

abbrev appendEventLaw
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendEventLaw prior (appendNextAtom actionCarrier)

abbrev appendSource
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendSource prior (appendNextAtom actionCarrier)

abbrev appendEmitted
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    (current : (AppendVAt prior actionCarrier).Current) :=
  rootedAppendEmitted prior (appendNextAtom actionCarrier) current

abbrev AppendExactTransitionAt
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    {current : (AppendVAt prior actionCarrier).Current} →
    (occurrence :
      (appendSource prior actionCarrier).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : NewN.Support} →
    OpenResponsibilityAt NewN
      ((appendSource prior actionCarrier).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt NewN targetSupport → Type :=
  RootedAppendExactTransitionAt prior (appendNextAtom actionCarrier)

abbrev appendWriteRowSource
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendWriteRowSource prior (appendNextAtom actionCarrier)

abbrev appendRows
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    {current : (AppendVAt prior actionCarrier).Current}
    (occurrence :
      (appendSource prior actionCarrier).toRootSource.actual.OccurrenceAt current) :=
  rootedAppendRows prior (appendNextAtom actionCarrier) occurrence

abbrev appendPatch
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    {current : (AppendVAt prior actionCarrier).Current}
    (occurrence :
      (appendSource prior actionCarrier).toRootSource.actual.OccurrenceAt current) :=
  rootedAppendPatch prior (appendNextAtom actionCarrier) occurrence

abbrev appendLedgerCompiler
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendLedgerCompiler prior (appendNextAtom actionCarrier)

abbrev appendRestructuringLaw
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendRestructuringLaw prior (appendNextAtom actionCarrier)

theorem appendPatch_origin_eq
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    (current : (AppendVAt prior actionCarrier).Current) (event : PUnit)
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    ((appendPatch prior actionCarrier (current := current)
      ⟨minimalCoface.cofaceSupport, event⟩).toLedgerWriteEvolution.origin
        entry).1 = entry :=
  rootedAppendPatch_origin_eq prior (appendNextAtom actionCarrier)
    current event entry

theorem appendPatch_destination_eq
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    (current : (AppendVAt prior actionCarrier).Current) (event : PUnit)
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    ((appendPatch prior actionCarrier (current := current)
      ⟨minimalCoface.cofaceSupport, event⟩).toLedgerWriteEvolution.destination
        entry).1 = entry :=
  rootedAppendPatch_destination_eq prior (appendNextAtom actionCarrier)
    current event entry

abbrev appendRestructuringCompiler
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendRestructuringCompiler prior (appendNextAtom actionCarrier)

abbrev appendRestructuringSource
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendRestructuringSource prior (appendNextAtom actionCarrier)

abbrev appendFirstSuccessor
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  rootedAppendFirstSuccessor prior (appendNextAtom actionCarrier)

@[simp] theorem appendFirstSuccessor_target_exact
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    (appendFirstSuccessor prior actionCarrier).targetCurrent =
      appendedCriticalSelectionCurrent prior actionCarrier :=
  rootedAppendFirstSuccessor_target_exact prior (appendNextAtom actionCarrier)

theorem appendLedger_directConsumer
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    (appendSource prior actionCarrier).initial = prior ∧
      (appendFirstSuccessor prior actionCarrier).targetCurrent =
        appendedCriticalSelectionCurrent prior actionCarrier ∧
      (appendedCriticalSelectionCurrent prior actionCarrier).root =
        actionCarrier.action.criticalBearer.bearerLineage.seed ∧
      (appendRows prior actionCarrier
        (appendEmitted prior actionCarrier prior)).size = 2 ∧
      appendNativeTarget prior actionCarrier
          (appendedCriticalSelectionCurrent prior actionCarrier) =
        retainedSelectionNext
          (appendedCriticalSelectionCurrent prior actionCarrier) :=
  rootedAppendLedger_directConsumer prior (appendNextAtom actionCarrier)

end
end M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendLedger.appendedCriticalSelectionCurrent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendLedger.appendLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendLedger.appendRestructuringSource
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendLedger.appendLedger_directConsumer
