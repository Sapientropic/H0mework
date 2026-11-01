import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.SourceGeneratedCriticalEventSelectionRevisedLedger

/-!
# Revised-root inquiry source

The U8 target needs one installed inquiry coordinate before its emitter can
participate in the canonical runtime.  This file supplies the root-semantic
theory, a source-native U7 calculus and the exact emitted-support entry used by
later actual-action compiler images.  It creates no root, ledger, action or
future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCriticalEventSelectionRevisedInquiry

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger

def revisedInquiryDefaultEntry
    (support : NewN.Support) : OpenResponsibilityAt NewN support := by
  cases support with
  | inl oldSupport =>
      cases oldSupport <;> exact ⟨.inl (), ()⟩
  | inr direction =>
      cases direction
      exact newRevisedEntry

def revisedInquiryU7 : U7ProducerCalculus NewN where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def revisedInquiryU7Source :
    U7ActualSuccessorSource NewN revisedInquiryU7 where
  EventAt := SourceGeneratedU7DemandAt revisedInquiryU7
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _ =>
    revisedInquiryDefaultEntry support

def revisedInquiryCalculus :
    U7ObstructionEvolutionCalculus NewN revisedInquiryU7 where
  source := revisedInquiryU7Source
  compile := by
    intro indexedSupport indexedObstruction demand event
    cases indexedSupport with
    | inl oldSupport =>
        exact
          { disposition := .redirected ⟨(), rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred () rfl rfl
                (Nat.le_refl _), rfl⟩ }
    | inr direction =>
        cases direction
        exact
          { disposition := .redirected
              ⟨GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget (),
                rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred
                (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
                rfl rfl (Nat.le_refl _), rfl⟩ }

def revisedInquiryTheory : TheoryState NewN :=
  TheoryState.rootSemantic NewN

def revisedInquiryEntryAt
    (_current : EssentialAccessCriticalSelectionCurrent) :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  newRevisedEntry

def revisedInquiryAuditAt
    (_current : EssentialAccessCriticalSelectionCurrent) :
    SourceNativeInquiryFrontAuditAt revisedInquiryU7 revisedInquiryCalculus
      revisedInquiryTheory minimalCoface.cofaceSupport :=
  .answered

end
end M14SourceGeneratedCriticalEventSelectionRevisedInquiry
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedInquiry.revisedInquiryCalculus
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedInquiry.revisedInquiryAuditAt
