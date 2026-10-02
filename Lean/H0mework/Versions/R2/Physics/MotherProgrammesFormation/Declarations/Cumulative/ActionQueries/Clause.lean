import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Inputs
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.ProgramConsumer

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open MotherInquiryAnswerOperands
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query : Type} (query : Query)
    {entry : MotherNativeAuthority.EntryAt root visit.current}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "canonical" => root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit

abbrev TargetAt (pair : MotherNativeAuthority.AuthorityTotal root visit) :=
  SourceNativeSequentialActualActionTargetAt root visit canonical pair.1 pair.2

def targetCompilation (target : TargetAt (root := root) (visit := visit) ⟨entry, authority⟩) :
    Compilation query entry authority calculus :=
  .actualAction ((MotherNativeAction.restore target).generate canonical)

def IsAction : Compilation query entry authority calculus → Prop
  | .actualAction .. => True
  | _ => False

/-- Canonical-event elimination retains the full target of every original
action compilation. No arbitrary-event input space is formed. -/
theorem action_target (compiled : Compilation query entry authority calculus)
    (isAction : IsAction calculus query compiled) :
    ∃ target : TargetAt (root := root) (visit := visit) ⟨entry, authority⟩,
      targetCompilation calculus query target = compiled := by
  cases compiled with
  | @actualAction program sourceEvent generated =>
    cases SourceNativeTemporalVisitGeneratedEvolutionAt.eq_generated sourceEvent
    exact ⟨MotherNativeAction.read program,
      MotherNativeAction.complete_compilation_recovers program canonical generated⟩
  | answered => cases isAction
  | u7Answered => cases isAction
  | oldLanguageAnswered => cases isAction
  | requiresU8 => cases isAction

def formClause (actual : MotherNativeAuthority.AuthorityTotal root visit)
    (target : TargetAt actual) (projection : Projection root) :
    Option (MotherNativeClause.Clause root visit U7 calculus query) :=
  MotherInquiryAnswerClause.formAtAuthority calculus query (targetCompilation calculus query target) projection

def formClauseWithAuthority {old : MotherNativeAuthority.AuthorityTotal root visit}
    (actual : MotherNativeAuthority.AuthorityTotal root visit) (same : actual = old)
    (target : TargetAt old) (projection : Projection root) :
    Option (MotherNativeClause.Clause root visit U7 calculus query) :=
  formClause calculus query actual (Eq.mp (congrArg TargetAt same.symm) target) projection

theorem formClause_recovers (clause : MotherNativeClause.Clause root visit U7 calculus query)
    (target : TargetAt (root := root) (visit := visit) ⟨clause.entry, clause.authority⟩)
    (compiledSame : targetCompilation calculus query target = clause.program.generate.output) :
    formClause calculus query ⟨clause.entry, clause.authority⟩ target clause.face.projection = some clause := by
  unfold formClause
  rw [compiledSame]
  exact MotherInquiryAnswerClause.formAtAuthority_recovers calculus query clause

theorem formClauseWithAuthority_recovers (clause : MotherNativeClause.Clause root visit U7 calculus query)
    (actual : MotherNativeAuthority.AuthorityTotal root visit)
    (same : actual = ⟨clause.entry, clause.authority⟩)
    (target : TargetAt (root := root) (visit := visit) ⟨clause.entry, clause.authority⟩)
    (compiledSame : targetCompilation calculus query target = clause.program.generate.output)
    (projection : Projection root) (projectionSame : projection = clause.face.projection) :
    formClauseWithAuthority calculus query actual same target projection = some clause := by
  cases same
  rw [projectionSame]
  exact formClause_recovers calculus query clause target compiledSame

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
