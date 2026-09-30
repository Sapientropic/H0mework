import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeAction.Elimination
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.RowRecovery

/-! Actual-action fields already determined by the complete original root
are eliminated through that root's native consumers, without fresh fields. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionRecovery
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
universe u

variable {N : WorldRelationNetwork.{u}}

def semanticTranslation (theory : TheoryState N) :
    ConservativeTheoryTranslation theory (TheoryState.rootSemantic N) where
  compile := theory.denotes
  commuting := fun _ => rfl

theorem semanticTranslation_recovers (theory : TheoryState N)
    (original : ConservativeTheoryTranslation theory (TheoryState.rootSemantic N)) :
    semanticTranslation theory = original := by
  cases original with
  | mk compile commuting =>
    have same : @compile = @theory.denotes := by
      funext support expression
      exact commuting expression
    cases same
    rfl

theorem successor_recovers {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? generated = some successor := by
  cases generated <;> cases successor <;> rfl

variable {V : ConstructiveRoot.Vocabulary.{u}} {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit event entry authority

theorem targetTheory_recovers (target : Target) : target.targetRoot.source.base.lawSurface = target.targetTheory :=
  eq_of_heq target.lawSurface_heq

theorem targetRow_recovers (target : Target) :
    (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite target.targetRoot.toAuthoritativeRoot.toRoot.initialVisit)).canonicalGeneratedEntryRow?
        (target.initialOpenLedger.forward entry) = some target.translatedSourceEntryRow :=
  MotherNativeAuthority.row_selector_recovers _ _ target.translatedSourceEntryRow

theorem targetSuccessor_recovers (target : Target) :
    SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
      (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (.finite target.targetRoot.toAuthoritativeRoot.toRoot.initialVisit)).wholeLedgerWriteBack =
      some target.firstSuccessor := successor_recovers _ target.firstSuccessor

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionRecovery
