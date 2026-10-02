import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.Root

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLivingInquiryAlignment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

universe u
variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {Query FormedQuery : Type u} (queries : Query ≃ FormedQuery)

/-- A formed query address retains its original root-payload label. The
family records that interpretation explicitly instead of identifying types
or changing the literal query in the existing face token. -/
abbrev ClauseAtAddress (query : FormedQuery) :=
  MotherNativeClause.Clause root visit U7 calculus (queries.symm query)

def queryClauseEquiv :
    ((query : Query) → MotherNativeClause.Clause root visit U7 calculus query) ≃
      ((query : FormedQuery) → ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query) :=
  Equiv.piCongr queries (fun query =>
    Equiv.cast (congrArg (fun value : Query => MotherNativeClause.Clause root visit U7 calculus value)
      (queries.symm_apply_apply query).symm))

def queryClauseTotalEquiv :
    MotherNativeClause.Total root visit U7 calculus Query ≃
      (Σ query : FormedQuery, ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query) :=
  Equiv.sigmaCongr queries (fun query =>
    Equiv.cast (congrArg (fun value : Query => MotherNativeClause.Clause root visit U7 calculus value)
      (queries.symm_apply_apply query).symm))

theorem queryClauseTotal_projects (point : MotherNativeClause.Total root visit U7 calculus Query) :
    (queryClauseTotalEquiv queries point).1 = queries point.1 := rfl

def restrictQueryClauses
    (actual : (query : FormedQuery) → ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query) :
    (query : Query) → MotherNativeClause.Clause root visit U7 calculus query :=
  (queryClauseEquiv queries).symm actual

theorem restrictQueryClauses_eq
    (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query)
    (actual : (query : FormedQuery) → ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query)
    (formed : actual = queryClauseEquiv queries original) :
    restrictQueryClauses queries actual = original :=
  (congrArg (queryClauseEquiv queries).symm formed).trans ((queryClauseEquiv queries).symm_apply_apply original)

def assembleQueryRestriction
    (actual : (query : FormedQuery) → ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query) :
    RootInquiryStateAt N V :=
  MotherNativeClause.assemble (restrictQueryClauses queries actual)

theorem assembleQueryRestriction_eq
    (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query)
    (actual : (query : FormedQuery) → ClauseAtAddress (root := root) (visit := visit) (calculus := calculus) queries query)
    (formed : actual = queryClauseEquiv queries original) :
    assembleQueryRestriction queries actual = MotherNativeClause.assemble original :=
  congrArg MotherNativeClause.assemble (restrictQueryClauses_eq queries original actual formed)

theorem original_query_state_recovers (state : RootInquiryStateAt N V)
    {FormedQuery : Type u} (queries : state.Query ≃ FormedQuery)
    (actual : (query : FormedQuery) → ClauseAtAddress (root := state.root) (visit := state.visit)
      (calculus := state.calculus) queries query)
    (formed : actual = queryClauseEquiv queries (MotherNativeClause.ofState state)) :
    assembleQueryRestriction queries actual = state :=
  (assembleQueryRestriction_eq queries (MotherNativeClause.ofState state) actual formed).trans
    (MotherNativeClause.assemble_ofState state)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLivingInquiryAlignment
