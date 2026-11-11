import H0mework.Foundation.Inquiry.Protocol
import H0mework.Foundation.Runtime.GatedClaimProcess

/-!
# Inquiry boundary of a gated claim obstruction

The existing debt-U7 calculus produces the exact theory-audit gate.  That gate
is not yet a completed inquiry: it must be followed by an old-language answer
or an actual expressibility failure.  Consequently it cannot be converted to
an old process successor, and U8 remains unavailable without the latter typed
failure.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace GatedClaimObstructionInquiryBoundary

open DebtActivationWorld GatedClaimPreProcess PendingClaimBirth
open RootGeneratedDebtActivationU7 RootInquiryCompletion

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}}
variable {facade : SourceNativePendingClaimRuntimeFacade N}
variable {runtime : LivingRuntimeState facade.base.process}
variable {activated : ExactActivatedRootOccurrenceAt runtime}
variable {face : facade.PendingFaceAt runtime}
variable {read : SourceInstalledPendingClaimFaceAt facade runtime face}
variable {birth : SourceExactPendingClaimBirthReceiptAt
  facade runtime activated read}
variable {state : birth.law.DebtState}
variable {current : SourceNativeGatedClaimCurrentAt birth state}
variable (obstruction : SourceNativeGatedClaimObstructionAt current)
variable (oldU7 : U7ProducerCalculus N)
variable (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)

abbrev calculus := extendU7Calculus (law := birth.law) oldU7 oldCalculus

def event := (calculus oldU7 oldCalculus).source.emit
  obstruction.worldObstruction

def theoryAudit : SourceNativeU7TheoryAuditAt
    (calculus oldU7 oldCalculus) (event obstruction oldU7 oldCalculus) :=
  obstruction.toTheoryAudit oldU7 oldCalculus

theorem demandEntry_eq :
    U7ActualSuccessorSource.demandEntry
      (event obstruction oldU7 oldCalculus) = current.entry :=
  RootGeneratedDebtActivationU7.debt_demand_entry oldU7 oldCalculus
    birth.sourceLedger.support obstruction.event

/-- A compiler-certified theory audit excludes both immediate U7 answer
branches. -/
theorem no_u7Answer_of_theoryAudit :
    IsEmpty (SourceNativeU7AnswersAt (calculus oldU7 oldCalculus)
      obstruction.worldObstruction) := by
  constructor
  intro answer
  simp only [SourceNativeU7AnswersAt] at answer
  unfold U7ObstructionEvolutionCalculus.generated at answer
  unfold calculus at answer
  unfold SourceNativeGatedClaimObstructionAt.worldObstruction at answer
  unfold SourceNativeGatedClaimCurrentAt.ledger at answer
  unfold DebtActivationLedger.activeLedger at answer
  dsimp only at answer
  rw [RootGeneratedDebtActivationU7.debt_compiled_disposition] at answer
  exact nomatch answer

/-- U7 audit alone cannot complete the one-shot inquiry.  With neither a
lawful old-language answer nor actual expressibility failure, every inquiry
constructor is empty. -/
theorem inquiryAudit_isEmpty_without_answer_or_failure
    (oldTheory : TheoryState (ExtendedNetwork N birth.law))
    (answerEmpty : IsEmpty
      (OldLanguageAnswerAt oldTheory obstruction.worldObstruction))
    (failureEmpty : IsEmpty
      (ActualExpressibilityFailure oldTheory obstruction.worldObstruction)) :
    IsEmpty (SourceNativeInquiryAuditAt
      (extendU7 (law := birth.law) oldU7)
      (calculus oldU7 oldCalculus) oldTheory obstruction.worldObstruction) :=
  ⟨fun audit => by
    cases audit with
    | u7Answered answer =>
        exact (no_u7Answer_of_theoryAudit obstruction oldU7 oldCalculus).false
          answer
    | oldLanguageAnswered _ answer => exact answerEmpty.false answer
    | requiresU8 _ failure => exact failureEmpty.false failure⟩

/-- The complete root-semantic theory already expresses and realizes every
world obstruction, so this audit cannot manufacture a U8 failure. -/
theorem rootSemantic_failure_isEmpty :
    IsEmpty (ActualExpressibilityFailure
      (TheoryState.rootSemantic (ExtendedNetwork N birth.law))
      obstruction.worldObstruction) :=
  TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty
    (ExtendedNetwork N birth.law) obstruction.worldObstruction

/-- In the maximally faithful root-semantic theory the debt obstruction has
both its literal expression and its active debt-holds realization. -/
def rootSemanticOldLanguageAnswer : OldLanguageAnswerAt
    (TheoryState.rootSemantic (ExtendedNetwork N birth.law))
    obstruction.worldObstruction where
  expression := ⟨(ExtendedNetwork N birth.law).obstructionClaim
    obstruction.worldObstruction, rfl⟩
  realization := by
    unfold SourceNativeGatedClaimObstructionAt.worldObstruction
    exact ULift.up (PLift.up rfl)

/-- The exact root-semantic inquiry outcome is old-language answered, not U8.
It still has no gated next and does not settle the claim. -/
def rootSemanticInquiryAudit : SourceNativeInquiryAuditAt
    (extendU7 (law := birth.law) oldU7)
    (calculus oldU7 oldCalculus)
    (TheoryState.rootSemantic (ExtendedNetwork N birth.law))
    obstruction.worldObstruction :=
  .oldLanguageAnswered (theoryAudit obstruction oldU7 oldCalculus)
    (rootSemanticOldLanguageAnswer obstruction)

/-- A gated obstruction has no ordinary continuation even though an unrelated
fixed living process always has a source-owned successor.  Hence their next
carriers cannot be identified. -/
theorem no_equiv_with_livingProcess_successor
    {M : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess M)
    (processState : process.State) :
    IsEmpty (obstruction.GeneratedNextAt ≃
      { successor : process.State //
        (process.stateAt processState).IsGeneratedSuccessor
          (process.stateAt successor) }) :=
  ⟨fun equivalence => nomatch equivalence.symm (process.successorAt processState)⟩

end

end GatedClaimObstructionInquiryBoundary
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
