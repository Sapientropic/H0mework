import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeProgram.Clause
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.Section
import H0mework.Foundation.Inquiry.Engine

/-! Direct original inquiry consumption after literal complete-root recovery.
The clause section remains an explicit source-formation responsibility; this
module is the dependent transporter, not a producer of missing clauses. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLivingInquiryAlignment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

universe u
variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}

structure Declaration (root : SourceNativeLivingRootClosure N V) : Type (u + 12) where
  visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot
  U7 : U7ProducerCalculus N
  calculus : U7ObstructionEvolutionCalculus N U7
  Query : Type u
  clauses : ∀ query : Query, MotherNativeClause.Clause root visit U7 calculus query

def assemble {root : SourceNativeLivingRootClosure N V} (declaration : Declaration root) : RootInquiryStateAt N V :=
  MotherNativeClause.assemble declaration.clauses

def ofState (state : RootInquiryStateAt N V) : Declaration state.root where
  visit := state.visit
  U7 := state.U7
  calculus := state.calculus
  Query := state.Query
  clauses := MotherNativeClause.ofState state

theorem assemble_ofState (state : RootInquiryStateAt N V) : assemble (ofState state) = state :=
  MotherNativeClause.assemble_ofState state

def declarationEquiv {original restored : SourceNativeLivingRootClosure N V}
    (same : restored = original) : Declaration original ≃ Declaration restored :=
  Equiv.cast (congrArg Declaration same.symm)

/-- The actual restored root is installed before all dependent clause
fields. Only the proved literal equality transports their original indices. -/
def assembleRestored {original : SourceNativeLivingRootClosure N V}
    (restored : SourceNativeLivingRootClosure N V) (same : restored = original)
    (declaration : Declaration original) : RootInquiryStateAt N V :=
  assemble (declarationEquiv same declaration)

theorem assembleRestored_eq {original : SourceNativeLivingRootClosure N V}
    (restored : SourceNativeLivingRootClosure N V) (same : restored = original)
    (declaration : Declaration original) : assembleRestored restored same declaration = assemble declaration := by
  cases same
  rfl

theorem assembleRestored_root {original : SourceNativeLivingRootClosure N V}
    (restored : SourceNativeLivingRootClosure N V) (same : restored = original)
    (declaration : Declaration original) : (assembleRestored restored same declaration).root = restored := rfl

theorem state_recovers (state : RootInquiryStateAt N V)
    (restored : SourceNativeLivingRootClosure N V) (same : restored = state.root) :
    assembleRestored restored same (ofState state) = state :=
  (assembleRestored_eq restored same (ofState state)).trans (assemble_ofState state)

/-- Root recovery preserves the complete compiler record, exact installed
face, Type-valued authority and the original U7/whole-ledger equation. -/
theorem dependent_fields_of_eq {first last : RootInquiryStateAt N V} (same : first = last)
    (query : first.Query) :
    let other := Equiv.cast (congrArg (fun state : RootInquiryStateAt N V => state.Query) same) query
    HEq (first.authorityAt query) (last.authorityAt other) ∧
    HEq (first.compilationProgramAt query) (last.compilationProgramAt other) ∧
    HEq (first.compilationFaceAt query) (last.compilationFaceAt other) ∧
    HEq (first.u7RootDisposition_commutes query) (last.u7RootDisposition_commutes other) := by
  cases same
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem compile_of_eq {first last : RootInquiryStateAt N V} (same : first = last)
    (query : first.Query) :
    HEq (first.compileInquiry query)
      (last.compileInquiry (Equiv.cast (congrArg (fun state : RootInquiryStateAt N V => state.Query) same) query)) := by
  cases same
  rfl

theorem compile_at_every_event {root : SourceNativeLivingRootClosure N V}
    (declaration : Declaration root) (query : declaration.Query)
    (event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot declaration.visit) :
    (assemble declaration).compileInquiry query = (declaration.clauses query).program.compile event :=
  MotherNativeClause.compile_at_every_event declaration.clauses query event

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLivingInquiryAlignment
