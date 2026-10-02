import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.AnswerFormation
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.Query
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityFamilies.Coverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryQuery
open MotherLivingInquiryAlignment MotherInquiryAnswerClause
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section
universe u v
private theorem cast_family {A : Type u} {F : A → Type v} (f : (a : A) → F a)
    {first last : A} (same : first = last) : Equiv.cast (congrArg F same) (f first) = f last := by
  cases same
  rfl

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query : Type} (base : MotherArenaHigher.Material rank) (queries : Query ≃ MotherAuthorityFamilies.Member base)
    (operand : Operand root visit ↪ MotherArenaHigher.Base rank)

/-- The complete query carrier is the actual material subtype. The inverse
label interpretation keeps every original face/program index unchanged. -/
def formAtQueries (material : MotherArenaHigher.Material rank) :
    Option ((query : MotherAuthorityFamilies.Member base) →
      ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query) :=
  (MotherArenaReceipts.NativeSection.form
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member base ↪ MotherArenaHigher.Base rank)
    (fun _ => operand) material).bind (fun inputs =>
      if complete : ∀ query, (MotherInquiryAnswerClause.form calculus (queries.symm query) (inputs query)).isSome then
        some (fun query => (MotherInquiryAnswerClause.form calculus (queries.symm query) (inputs query)).get (complete query))
      else none)

theorem every_at_queries
    (clauses : (query : MotherAuthorityFamilies.Member base) →
      ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query)
    (answering : ∀ query, Answering calculus (queries.symm query) (clauses query).program.generate.output) :
    ∃ material : MotherArenaHigher.Material rank,
      formAtQueries calculus base queries operand material = some clauses := by
  have allInputs := fun query => every_answering_clause calculus (queries.symm query) (clauses query) (answering query)
  choose inputs inputFormed using allInputs
  obtain ⟨material, selected⟩ := MotherArenaReceipts.NativeSection.every_section
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member base ↪ MotherArenaHigher.Base rank)
    (fun _ => operand) inputs
  have complete : ∀ query, (MotherInquiryAnswerClause.form calculus (queries.symm query) (inputs query)).isSome := by
    intro query
    rw [inputFormed]
    rfl
  refine ⟨material, ?_⟩
  simp only [formAtQueries, selected, Option.bind_some, dif_pos complete]
  apply congrArg some
  funext query
  exact Option.some.inj ((Option.some_get (complete query)).trans (inputFormed query))

theorem query_clause_at (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query)
    (query : MotherAuthorityFamilies.Member base) :
    queryClauseEquiv queries original query = original (queries.symm query) := by
  obtain ⟨originalQuery, rfl⟩ := queries.surjective query
  rw [queryClauseEquiv, Equiv.piCongr_apply_apply]
  exact cast_family original (queries.symm_apply_apply originalQuery).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryQuery
