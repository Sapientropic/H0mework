import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AnswerQueries.Readback
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AnswerQueries.Layout
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquirySource.Assembly
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquirySource.HeaderOrigin
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.World

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {Index : Type}

/-- The complete original Query and the answering fragment have separate
formed carriers. Current, outer calculus, labels and every clause are all
actual source outputs at the same rank. -/
structure Origin (state : RootInquiryStateAt N V) (label : Index → state.Query) where
  materials : Materials rank
  current : MotherNativeCurrent.Restriction rank (MotherInquirySource.currentOf state) materials.current
  header : MotherInquirySource.HeaderOrigin (rank := rank) state.U7 state.calculus
  header_materials : materials.header = (header.demandMaterial, header.eventMaterial, header.compilerMaterial)
  queries : state.Query ≃ MotherAuthorityFamilies.Member materials.queries
  indices : Index ≃ MotherAuthorityFamilies.Member materials.indices
  operand : MotherInquiryAnswerClause.Operand state.root state.visit ↪ MotherArenaHigher.Base rank
  available : (form state.calculus materials.queries materials.indices queries operand materials.clauses).isSome
  labelsRecovered : ∀ index,
    ((form state.calculus materials.queries materials.indices queries operand materials.clauses).get available).1
      (indices index) = queries (label index)
  clausesRecovered : ∀ index,
    readClause state.calculus materials.queries materials.indices queries indices label
      ((form state.calculus materials.queries materials.indices queries operand materials.clauses).get available)
      labelsRecovered index = MotherNativeClause.ofState state (label index)

variable {state : RootInquiryStateAt N V} {label : Index → state.Query} (origin : Origin (rank := rank) state label)

def Origin.value :=
  (form state.calculus origin.materials.queries origin.materials.indices origin.queries origin.operand origin.materials.clauses).get origin.available

def Origin.readLabel (index : Index) : state.Query := origin.queries.symm (origin.value.1 (origin.indices index))

theorem Origin.readLabel_eq (index : Index) : origin.readLabel index = label index :=
  (congrArg origin.queries.symm (origin.labelsRecovered index)).trans (origin.queries.symm_apply_apply _)

def Origin.readClauses (index : Index) : MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label index) :=
  readClause state.calculus origin.materials.queries origin.materials.indices origin.queries origin.indices label
    origin.value origin.labelsRecovered index

theorem Origin.readClauses_eq : origin.readClauses = fun index => MotherNativeClause.ofState state (label index) :=
  funext origin.clausesRecovered

def Origin.readWorldCurrent : Σ network : WorldRelationNetwork.{0}, SourceNativeLivingRootCurrentAt network :=
  MotherNativeCurrent.world origin.current.presentation.authority.network origin.current.read

theorem Origin.readWorldCurrent_eq : origin.readWorldCurrent = ⟨N, MotherInquirySource.currentOf state⟩ := by
  unfold Origin.readWorldCurrent
  rw [MotherNativeCurrent.world_eq, origin.current.read_eq]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
