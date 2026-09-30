import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Clause
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Calculus

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherInquiryAnswerOperands MotherU8Revision
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {Query : Type} {query : Query}
    {entry : OpenResponsibilityAt N (Support root visit)}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

def IsU8 : Compilation query entry authority calculus → Prop
  | .requiresU8 .. => True
  | _ => False

structure Data (clause : MotherNativeClause.Clause root visit U7 calculus query) where
  obstruction : N.ObstructionAt (Support root visit)
  gate : SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1
  failure : ActualExpressibilityFailure (Theory root) obstruction
  core : SourceGeneratedInquiryU8RevisionCoreAt root visit U7 calculus (Theory root) query
    (InquiryEvent (root := root) (visit := visit)) clause.entry clause.authority obstruction gate failure
  compiled_eq : clause.program.generate.output = .requiresU8 obstruction gate failure core

theorem exists_data (clause : MotherNativeClause.Clause root visit U7 calculus query)
    (u8 : IsU8 clause.program.generate.output) : Nonempty (Data clause) := by
  cases output : clause.program.generate.output with
  | requiresU8 obstruction gate failure core => exact ⟨⟨obstruction, gate, failure, core, output⟩⟩
  | answered => simp only [output, IsU8] at u8
  | u7Answered => simp only [output, IsU8] at u8
  | oldLanguageAnswered => simp only [output, IsU8] at u8
  | actualAction => simp only [output, IsU8] at u8

variable {Index : Type} (state : RootInquiryStateAt N V) (label : Index → state.Query)
    (data : (index : Index) → Data (MotherNativeClause.ofState state (label index)))

def sourceCurrent : SourceNativeLivingRootCurrentAt N := ⟨V, state.root, state.visit⟩

def nextCurrent (index : Index) : SourceNativeLivingRootCurrentAt (data index).core.revision.generate.NewN :=
  ⟨(data index).core.revision.generate.NewV, (data index).core.revision.generate.newLivingRoot,
    .finite (data index).core.revision.generate.newLivingRoot.toAuthoritativeRoot.toRoot.initialVisit⟩

def networks : Unit ⊕ Index → WorldRelationNetwork.{0}
  | .inl _ => N
  | .inr index => (data index).core.revision.generate.NewN

def currents : (index : Unit ⊕ Index) → SourceNativeLivingRootCurrentAt (networks state label data index)
  | .inl _ => sourceCurrent state
  | .inr index => nextCurrent state label data index

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
