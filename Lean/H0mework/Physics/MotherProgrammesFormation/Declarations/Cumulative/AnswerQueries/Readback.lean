import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AnswerQueries.Factory

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherInquiryAnswerClause
open scoped Classical
noncomputable section

universe u v
private theorem cast_family {A : Type u} {F : A → Type v} (f : (a : A) → F a)
    {first last : A} (same : first = last) : Eq.mp (congrArg F same) (f first) = f last := by
  cases same
  rfl

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query Index : Type} {rank : Ordinal.{0}}
    (queryBase indexBase : MotherArenaHigher.Material rank)
    (queries : Query ≃ MotherAuthorityFamilies.Member queryBase)
    (indices : Index ≃ MotherAuthorityFamilies.Member indexBase)
    (label : Index → Query)

def readClause (value : Value (root := root) (visit := visit) calculus queryBase indexBase queries)
    (commutes : ∀ index, value.1 (indices index) = queries (label index)) (index : Index) :
    MotherNativeClause.Clause root visit U7 calculus (label index) :=
  Eq.mp (congrArg (fun query => MotherNativeClause.Clause root visit U7 calculus query)
    ((congrArg queries.symm (commutes index)).trans (queries.symm_apply_apply (label index))))
      (value.2 (indices index))

theorem readClause_original (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query)
    (labels : Labels queryBase indexBase)
    (commutes : ∀ index, labels (indices index) = queries (label index)) (index : Index) :
    readClause calculus queryBase indexBase queries indices label
      ⟨labels, fun index => original (queries.symm (labels index))⟩ commutes index = original (label index) :=
  cast_family original ((congrArg queries.symm (commutes index)).trans (queries.symm_apply_apply (label index)))

theorem labelled_at_rank
    (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query)
    (answering : ∀ index, Answering calculus (label index) (original (label index)).program.generate.output)
    (operand : Operand root visit ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (form calculus queryBase indexBase queries operand material).isSome,
      ∃ commutes : ∀ index, ((form calculus queryBase indexBase queries operand material).get available).1
          (indices index) = queries (label index),
        ∀ index, readClause calculus queryBase indexBase queries indices label
          ((form calculus queryBase indexBase queries operand material).get available) commutes index = original (label index) := by
  let labels : Labels queryBase indexBase := fun index => queries (label (indices.symm index))
  let clauses : ClauseSection (root := root) (visit := visit) calculus queryBase indexBase queries labels :=
    fun index => original (queries.symm (labels index))
  have selectedAnswering : ∀ index, Answering calculus (queries.symm (labels index)) (clauses index).program.generate.output := by
    intro index
    dsimp only [labels, clauses]
    rw [queries.symm_apply_apply]
    exact answering (indices.symm index)
  obtain ⟨material, formed⟩ := every_labelled calculus queryBase indexBase queries operand labels clauses selectedAnswering
  have available : (form calculus queryBase indexBase queries operand material).isSome := by rw [formed]; rfl
  have outputSame : (form calculus queryBase indexBase queries operand material).get available = ⟨labels, clauses⟩ :=
    Option.some.inj ((Option.some_get available).trans formed)
  have labelsSame : ∀ index, labels (indices index) = queries (label index) := by
    intro index
    simp only [labels, indices.symm_apply_apply]
  have originalRecovered : ∃ commutes : ∀ index, labels (indices index) = queries (label index),
      ∀ index, readClause calculus queryBase indexBase queries indices label ⟨labels, clauses⟩ commutes index = original (label index) :=
    ⟨labelsSame, readClause_original calculus queryBase indexBase queries indices label original labels labelsSame⟩
  exact ⟨material, available, outputSame.symm ▸ originalRecovered⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
