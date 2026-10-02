import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquiryQuery.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.HeaderConsumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.Restriction

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquirySource
open MotherLivingInquiryAlignment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
universe u v
private theorem dependent_read_heq {A : Type u} {F : A → Type v} (read : (a : A) → F a)
    {first last : A} (same : first = last) : HEq (read first) (read last) := by
  cases same
  rfl

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

def currentOf (state : RootInquiryStateAt N V) : SourceNativeLivingRootCurrentAt N :=
  ⟨V, state.root, state.visit⟩

structure Fields (current : SourceNativeLivingRootCurrentAt N) where
  U7 : U7ProducerCalculus N
  calculus : U7ObstructionEvolutionCalculus N U7
  Query : Type
  clauses : (query : Query) → MotherNativeClause.Clause current.root current.visit U7 calculus query

def assemble (current : SourceNativeLivingRootCurrentAt N) (fields : Fields current) :
    Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, RootInquiryStateAt N vocabulary :=
  ⟨current.V, MotherNativeClause.assemble fields.clauses⟩

def fieldsOf (state : RootInquiryStateAt N V) : Fields (currentOf state) :=
  ⟨state.U7, state.calculus, state.Query, MotherNativeClause.ofState state⟩

theorem assemble_fieldsOf (state : RootInquiryStateAt N V) :
    assemble (currentOf state) (fieldsOf state) = ⟨V, state⟩ :=
  congrArg (Sigma.mk V) (MotherNativeClause.assemble_ofState state)

theorem clauses_of_state_eq (state : RootInquiryStateAt N V)
    (clauses : (query : state.Query) → MotherNativeClause.Clause state.root state.visit state.U7 state.calculus query)
    (same : MotherNativeClause.assemble clauses = state) : clauses = MotherNativeClause.ofState state :=
  eq_of_heq (dependent_read_heq MotherNativeClause.ofState same)

/-- Actual material header fields precede the complete original-label
clause section. Only their proved equality aligns the dependent indices. -/
def fieldsWithHeader (state : RootInquiryStateAt N V)
    (header : MotherInquiryU7Header.Header N) (same : header = ⟨state.U7, state.calculus⟩)
    (clauses : (query : state.Query) → MotherNativeClause.Clause state.root state.visit state.U7 state.calculus query) :
    Fields (currentOf state) where
  U7 := header.1
  calculus := header.2
  Query := state.Query
  clauses := Equiv.cast (congrArg (HeaderSection state.visit state.Query) same.symm) clauses

theorem fieldsWithHeader_eq (state : RootInquiryStateAt N V)
    (header : MotherInquiryU7Header.Header N) (same : header = ⟨state.U7, state.calculus⟩)
    (clauses : (query : state.Query) → MotherNativeClause.Clause state.root state.visit state.U7 state.calculus query)
    (clausesSame : clauses = MotherNativeClause.ofState state) :
    fieldsWithHeader state header same clauses = fieldsOf state := by
  cases same
  cases clausesSame
  rfl

def assembleCurrent (state : RootInquiryStateAt N V) (current : SourceNativeLivingRootCurrentAt N)
    (same : current = currentOf state) (fields : Fields (currentOf state)) :
    Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, RootInquiryStateAt N vocabulary :=
  assemble current (Equiv.cast (congrArg Fields same.symm) fields)

theorem assembleCurrent_recovers (state : RootInquiryStateAt N V) (current : SourceNativeLivingRootCurrentAt N)
    (same : current = currentOf state) (fields : Fields (currentOf state)) (fieldsSame : fields = fieldsOf state) :
    assembleCurrent state current same fields = ⟨V, state⟩ := by
  cases same
  cases fieldsSame
  exact assemble_fieldsOf state

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquirySource
