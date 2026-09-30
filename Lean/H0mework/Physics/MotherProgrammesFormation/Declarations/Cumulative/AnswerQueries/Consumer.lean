import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AnswerQueries.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {Index : Type} {state : RootInquiryStateAt N V} {label : Index → state.Query}
    (origin : Origin (rank := rank) state label)

private theorem clause_compile_heq {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {Query : Type} {query : Query}
    {first last : MotherNativeClause.Clause root visit U7 calculus query} (same : first = last) :
    HEq first.program.generate.output last.program.generate.output := by
  cases same
  rfl

theorem Origin.compile_recovers (index : Index) :
    HEq (origin.readClauses index).program.generate.output (state.compileInquiry (label index)) :=
  clause_compile_heq (congrFun origin.readClauses_eq index)

theorem Origin.compile_at_every_event (index : Index)
    (exactEvent : ExactTemporalCausalRootEventAt state.root.toAuthoritativeRoot.toLedgerRoot state.visit) :
    HEq ((origin.readClauses index).program.compile exactEvent) (state.compileInquiry (label index)) := by
  rw [MotherNativeProgram.compile_eq_generate]
  exact origin.compile_recovers index

abbrev AnsweringIndex (state : RootInquiryStateAt N V) :=
  {query : state.Query // MotherInquiryAnswerClause.Answering state.calculus query (state.compileInquiry query)}

/-- Every original state supplies its whole Query, current and outer header,
even when this answering fragment is empty. All answering labels and full
compilations are material readbacks at their original dependent indices. -/
theorem every_answering_fragment (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ origin : Origin (rank := rank) state (Subtype.val : AnsweringIndex state → state.Query),
        unpack material = origin.materials ∧
        origin.readClauses = (fun index : AnsweringIndex state => MotherNativeClause.ofState state index.val) ∧
        (∀ index : AnsweringIndex state, origin.readLabel index = index.val) ∧
        origin.readWorldCurrent = ⟨N, MotherInquirySource.currentOf state⟩ ∧
        origin.header.read = ⟨state.U7, state.calculus⟩ ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) :=
  every_answering_source N V state (AnsweringIndex state) Subtype.val (fun index => index.property)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
