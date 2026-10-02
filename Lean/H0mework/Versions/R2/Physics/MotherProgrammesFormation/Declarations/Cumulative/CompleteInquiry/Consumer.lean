import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.CompleteInquiry.Read

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {state : RootInquiryStateAt N V} (origin : Origin state)

private theorem compile_of_eq {first last : RootInquiryStatePresentation} (same : first = last)
    (query : first.Query) :
    HEq (first.state.base.compileInquiry query)
      (last.state.base.compileInquiry (Equiv.cast (congrArg RootInquiryStatePresentation.Query same) query)) := by
  cases same
  rfl

theorem Origin.compile_recovers (query : origin.readWorld.Query) :
    HEq (origin.readWorld.state.base.compileInquiry query)
      (state.compileInquiry (Equiv.cast (congrArg RootInquiryStatePresentation.Query origin.readWorld_eq) query)) :=
  compile_of_eq origin.readWorld_eq query

private theorem program_of_clause_eq {Query : Type} {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7} {query : Query}
    {first last : MotherNativeClause.Clause root visit U7 calculus query} (same : first = last)
    (event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit) :
    HEq (first.program.compile event) (last.program.compile event) := by cases same; rfl

theorem Origin.compile_at_every_event (query : state.Query)
    (event : ExactTemporalCausalRootEventAt state.root.toAuthoritativeRoot.toLedgerRoot state.visit) :
    HEq ((origin.clauses query).program.compile event) (state.compileInquiry query) := by
  have same := program_of_clause_eq (congrFun origin.clauses_eq query) event
  rw [MotherNativeProgram.compile_eq_generate] at same
  exact same

/-- Both whole parent material families survive at the common rank. This
covers their complete spaces, not only the values emitted on an active path. -/
theorem Origin.whole_material_spaces :
    Function.LeftInverse
      (fun material =>
        ((fun index => MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank index material),
          (fun index => MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank index material)))
      (fun materials => MotherMaterialJoin.Mixed.combine origin.highRank origin.lowRank materials.1 materials.2) :=
  MotherMaterialJoin.Mixed.whole_family_leftInverse origin.highRank origin.lowRank

/-- Every original complete inquiry, without an external address or branch
condition, is the exact full readback of one joined source material. -/
theorem every_complete_inquiry (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) :
    ∃ origin : Origin state,
      origin.readWorld = ⟨N, V, RootInquiryEngineStateAt.create state⟩ ∧
      (∀ query : origin.readWorld.Query,
        HEq (origin.readWorld.state.base.compileInquiry query)
          (state.compileInquiry (Equiv.cast (congrArg RootInquiryStatePresentation.Query origin.readWorld_eq) query))) ∧
      (∀ event : ExactTemporalCausalRootEventAt state.root.toAuthoritativeRoot.toLedgerRoot state.visit,
        ∀ query : state.Query, HEq ((origin.clauses query).program.compile event) (state.compileInquiry query)) := by
  obtain ⟨origin⟩ := every_source N V state
  exact ⟨origin, origin.readWorld_eq, origin.compile_recovers, fun event query => origin.compile_at_every_event query event⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
