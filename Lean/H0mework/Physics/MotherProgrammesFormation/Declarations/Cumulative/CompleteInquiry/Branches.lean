import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.CompleteInquiry.Sections

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V)

abbrev AnswerIndex := {query : state.Query //
  MotherInquiryAnswerClause.Answering state.calculus query (state.compileInquiry query)}
abbrev BranchIndex := AnswerIndex state ⊕ MotherActionQueries.ActionIndex state ⊕ MotherU8Compiler.U8Index state

def branchLabel : BranchIndex state → state.Query
  | .inl query => query.val
  | .inr (.inl query) => query.val
  | .inr (.inr query) => query.val

/-- Coverage eliminates the five original constructors. Source selection
itself is formed separately as a material graph. -/
theorem branchLabel_surjective : Function.Surjective (branchLabel state) := by
  intro query
  cases compiled : state.compileInquiry query with
  | answered =>
    exact ⟨.inl ⟨query, by simp only [compiled, MotherInquiryAnswerClause.Answering]⟩, rfl⟩
  | u7Answered =>
    exact ⟨.inl ⟨query, by simp only [compiled, MotherInquiryAnswerClause.Answering]⟩, rfl⟩
  | oldLanguageAnswered =>
    exact ⟨.inl ⟨query, by simp only [compiled, MotherInquiryAnswerClause.Answering]⟩, rfl⟩
  | actualAction =>
    exact ⟨.inr (.inl ⟨query, by simp only [compiled, MotherActionQueries.IsAction]⟩), rfl⟩
  | requiresU8 =>
    exact ⟨.inr (.inr ⟨query, by simp only [compiled, MotherU8Compiler.IsU8]⟩), rfl⟩

variable (answers : (index : AnswerIndex state) →
      MotherNativeClause.Clause state.root state.visit state.U7 state.calculus index.val)
    (actions : (index : MotherActionQueries.ActionIndex state) →
      MotherNativeClause.Clause state.root state.visit state.U7 state.calculus index.val)
    (revisions : (index : MotherU8Compiler.U8Index state) →
      MotherNativeClause.Clause state.root state.visit state.U7 state.calculus index.val)

def branchClauses : (index : BranchIndex state) →
    MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (branchLabel state index)
  | .inl query => answers query
  | .inr (.inl query) => actions query
  | .inr (.inr query) => revisions query

variable {rank : Ordinal.{0}}
    (queryCode : state.Query ↪ MotherArenaHigher.Base rank)
    (indexCode : BranchIndex state ↪ MotherArenaHigher.Base rank)

/-- All original branch interiors come from their formed subfamily. The
complete selection programme is paid by a separate source graph. -/
def formMixed (material : MotherArenaHigher.Material rank) :
    Option ((query : state.Query) → MotherNativeClause.Clause state.root state.visit state.U7 state.calculus query) :=
  formSection (branchLabel state) (branchClauses state answers actions revisions) queryCode indexCode material

theorem mixed_recovers
    (answersSame : ∀ index, answers index = MotherNativeClause.ofState state index.val)
    (actionsSame : ∀ index, actions index = MotherNativeClause.ofState state index.val)
    (revisionsSame : ∀ index, revisions index = MotherNativeClause.ofState state index.val) :
    ∃ material : MotherArenaHigher.Material rank,
      formMixed state answers actions revisions queryCode indexCode material = some (MotherNativeClause.ofState state) := by
  have covered : ∀ query, ∃ index, branchLabel state index = query := branchLabel_surjective state
  choose selection aligned using covered
  apply formSection_of_parent_recovery (branchLabel state) (branchClauses state answers actions revisions)
    queryCode indexCode selection aligned (MotherNativeClause.ofState state)
  intro index
  cases index with
  | inl query => exact answersSame query
  | inr rest =>
    cases rest with
    | inl query => exact actionsSame query
    | inr query => exact revisionsSame query

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
