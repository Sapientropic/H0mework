import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.CompleteInquiry.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherLivingInquiryAlignment
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {state : RootInquiryStateAt N V} (origin : Origin state)

/-- The final five-branch section lives on the actually formed whole Query
carrier, which remains complete even if an individual branch is empty. -/
def Origin.formedClauses :
    (query : MotherAuthorityFamilies.Member origin.answer.materials.queries) →
      ClauseAtAddress (root := state.root) (visit := state.visit) (calculus := state.calculus) origin.answer.queries query :=
  queryClauseEquiv origin.answer.queries origin.readClauses

def Origin.clauses : (query : state.Query) → MotherNativeClause.Clause state.root state.visit state.U7 state.calculus query :=
  restrictQueryClauses origin.answer.queries origin.formedClauses

theorem Origin.clauses_eq : origin.clauses = MotherNativeClause.ofState state := by
  unfold Origin.clauses Origin.formedClauses restrictQueryClauses
  rw [Equiv.symm_apply_apply]
  exact origin.readClauses_eq

/-- Actual complete current/header and all five full compiler branches are
assembled at the original dependency indices. -/
def Origin.read : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, RootInquiryStateAt N vocabulary :=
  MotherInquirySource.assembleCurrent state origin.answer.current.read origin.answer.current.read_eq
    (MotherInquirySource.fieldsWithHeader state origin.answer.header.read origin.answer.header.read_eq origin.clauses)

theorem Origin.read_eq : origin.read = ⟨V, state⟩ :=
  MotherInquirySource.assembleCurrent_recovers state origin.answer.current.read origin.answer.current.read_eq _
    (MotherInquirySource.fieldsWithHeader_eq state origin.answer.header.read origin.answer.header.read_eq origin.clauses origin.clauses_eq)

private def atNetwork (N G : WorldRelationNetwork.{0}) (same : G = N)
    (value : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, RootInquiryStateAt N vocabulary) : RootInquiryStatePresentation :=
  ⟨G, value.1, Equiv.cast (congrArg (fun network => RootInquiryEngineStateAt network value.1) same.symm)
    (RootInquiryEngineStateAt.create value.2)⟩

private theorem atNetwork_eq (N G : WorldRelationNetwork.{0}) (same : G = N)
    (value : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, RootInquiryStateAt N vocabulary) :
    atNetwork N G same value = ⟨N, value.1, RootInquiryEngineStateAt.create value.2⟩ := by cases same; rfl

/-- The network itself is an inverse read of the actual source field. -/
def Origin.readWorld : RootInquiryStatePresentation :=
  atNetwork N (MotherNetworkRestriction.restrictNetwork origin.answer.current.presentation.authority.network)
    (MotherNetworkRestriction.restrictNetwork_eq origin.answer.current.presentation.authority.network) origin.read

theorem Origin.readWorld_eq : origin.readWorld = ⟨N, V, RootInquiryEngineStateAt.create state⟩ := by
  unfold Origin.readWorld
  rw [atNetwork_eq, origin.read_eq]

/-- All original inquiry states have a complete same-material realization.
The returned origin determines its single joined material and rank. -/
theorem every_inquiry (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) :
    ∃ origin : Origin state, origin.readWorld = ⟨N, V, RootInquiryEngineStateAt.create state⟩ := by
  obtain ⟨origin⟩ := every_source N V state
  exact ⟨origin, origin.readWorld_eq⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
