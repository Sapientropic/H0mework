import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionBody
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "Program" => SourceNativeSequentialActualActionProgramAt root visit entry authority
local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit
  (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit) entry authority

theorem program_recovers (original : Program) (actualTarget : Target)
    (targetSame : actualTarget = MotherNativeAction.read original) :
    MotherNativeAction.restore actualTarget = original := by
  rw [targetSame, MotherNativeAction.restore_read]

variable {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {oldTheory : TheoryState N} {Query : Type} {query : Query}
    {InquiryEvent : Type 1} {event : InquiryEvent}

/-- The complete original compilation is preserved at every original exact
event. No separate arbitrary-event function space enters material formation. -/
theorem compilation_recovers (original : Program) (actualTarget : Target)
    (targetSame : actualTarget = MotherNativeAction.read original)
    (exactEvent : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit)
    (generated : SourceGeneratedSequentialActualActionAt original exactEvent) :
    (SourceNativeInquiryCompilationAt.actualAction
      ((MotherNativeAction.restore actualTarget).generate exactEvent) :
        SourceNativeInquiryCompilationAt root visit U7 calculus oldTheory query event entry authority) =
      .actualAction generated := by
  rw [targetSame]
  exact MotherNativeAction.complete_compilation_recovers original exactEvent generated

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionBody
