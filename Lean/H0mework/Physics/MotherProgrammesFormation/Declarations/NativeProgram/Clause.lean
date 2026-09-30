import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeProgram.Elimination

/-! The original dependent declaration fields are one native clause.
This receiver and its round trip are relative assembly; neither the header
nor the clause section acquires mother-source provenance from this packaging. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeClause

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

structure Clause {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query : Type u} (query : Query) where
  entry : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry
  program : SourceNativeInquiryCompilationProgramAt root visit U7 calculus
    root.toAuthoritativeRoot.source.lawSurface query
    (ULift.up.{u + 1, u} (root.emitted visit.current)) entry authority
  face : SourceNativeRootInquiryCompilationFaceCoreAt root visit query
    (ULift.up.{u + 1, u} (root.emitted visit.current)) entry authority program.generate.output
  dispositionCompatible :
    (obstruction : N.ObstructionAt
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) →
    (audit : SourceNativeInquiryAuditAt U7 calculus root.toAuthoritativeRoot.source.lawSurface obstruction) →
    program.generate.output.audit = .obstructed obstruction audit →
    U7DemandEntryRootDispositionCommutesAt calculus (calculus.source.emit obstruction) entry
      ((root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
        (root.emitted visit.current)).entryDisposition entry)

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
  {Query : Type u}

abbrev Total (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
    (Query : Type u) := Σ query : Query, Clause root visit U7 calculus query

def assemble (clauses : (query : Query) → Clause root visit U7 calculus query) :
    RootInquiryStateAt N V where
  root := root
  visit := visit
  U7 := U7
  calculus := calculus
  Query := Query
  entryAt := fun query => (clauses query).entry
  authorityAt := fun query => (clauses query).authority
  compilationProgramAt := fun query => (clauses query).program
  compilationFaceAt := fun query => (clauses query).face
  u7RootDisposition_commutes := fun query => (clauses query).dispositionCompatible

def ofState (state : RootInquiryStateAt N V) (query : state.Query) :
    Clause state.root state.visit state.U7 state.calculus query where
  entry := state.entryAt query
  authority := state.authorityAt query
  program := state.compilationProgramAt query
  face := state.compilationFaceAt query
  dispositionCompatible := state.u7RootDisposition_commutes query

theorem assemble_ofState (state : RootInquiryStateAt N V) : assemble (ofState state) = state := by
  cases state
  rfl

theorem compile_from_clause (clauses : (query : Query) → Clause root visit U7 calculus query)
    (query : Query) :
    (assemble clauses).compileInquiry query = (clauses query).program.generate.output := rfl

theorem compile_at_every_event (clauses : (query : Query) → Clause root visit U7 calculus query)
    (query : Query)
    (exactEvent : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit) :
    (assemble clauses).compileInquiry query = (clauses query).program.compile exactEvent :=
  (MotherNativeProgram.compile_eq_generate (clauses query).program exactEvent).symm

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeClause
