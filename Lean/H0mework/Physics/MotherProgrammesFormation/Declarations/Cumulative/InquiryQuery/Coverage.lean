import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquiryQuery.Answers

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryQuery
open MotherLivingInquiryAlignment MotherInquiryAnswerClause
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

/-- The material-created whole query carrier and all original answering
clauses form together. Inverse labels preserve the original dependent face
indices, and the complete original inquiry record is the actual readback. -/
theorem queries_at_rank (state : RootInquiryStateAt N V)
    (answering : ∀ query, Answering state.calculus query (state.compileInquiry query))
    (queryAddress : state.Query ↪ MotherArenaHigher.Base rank)
    (operandAddress : Operand state.root state.visit ↪ MotherArenaHigher.Base rank) :
    ∃ base : MotherArenaHigher.Material rank,
      ∃ queries : state.Query ≃ MotherAuthorityFamilies.Member base,
      ∃ material : MotherArenaHigher.Material rank,
        ∃ available : (formAtQueries state.calculus base queries operandAddress material).isSome,
          assembleQueryRestriction queries
            ((formAtQueries state.calculus base queries operandAddress material).get available) = state := by
  obtain ⟨base, ⟨queries⟩⟩ := MotherAuthorityFamilies.every_index state.Query queryAddress
  let original := MotherNativeClause.ofState state
  let clauses := queryClauseEquiv queries original
  have allAnswering : ∀ query, Answering state.calculus (queries.symm query) (clauses query).program.generate.output := by
    intro query
    dsimp only [clauses]
    rw [query_clause_at state.calculus base queries]
    exact answering (queries.symm query)
  obtain ⟨material, formed⟩ := every_at_queries state.calculus base queries operandAddress clauses allAnswering
  have available : (formAtQueries state.calculus base queries operandAddress material).isSome := by rw [formed]; rfl
  have same : (formAtQueries state.calculus base queries operandAddress material).get available = clauses :=
    Option.some.inj ((Option.some_get available).trans formed)
  exact ⟨base, queries, material, available, original_query_state_recovers state queries _ same⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryQuery
