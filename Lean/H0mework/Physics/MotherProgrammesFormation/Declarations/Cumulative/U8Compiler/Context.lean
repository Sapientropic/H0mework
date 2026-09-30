import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Data
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Transport
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Layout
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Family

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherInquiryAnswerOperands MotherU8Revision
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V) {Index : Type} (label : Index → state.Query)
    (data : (index : Index) → Data (MotherNativeClause.ofState state (label index)))
    {rank : Ordinal.{0}}
    {oldMaterials : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank}
    (old : MotherNativeCurrent.Restriction rank (sourceCurrent state) oldMaterials)
    (outer : MotherInquirySource.HeaderOrigin (rank := rank) state.U7 state.calculus)
    (index : Index)
    {newMaterials : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank}
    (new : MotherNativeCurrent.Restriction rank (nextCurrent state label data index) newMaterials)
    (face : MotherInquirySource.HeaderOrigin (rank := rank) state.U7 (data index).core.frontier.face.calculus)

def formAtContext (operand : Operand state.root state.visit) (material : MotherArenaHigher.Material rank) :
    Option (MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label index)) :=
  formOnContexts state.calculus (label index) (readCalculus face)
    ⟨(data index).core.revision.generate.NewN, (data index).core.revision.generate.NewV,
      (data index).core.revision.generate.newLivingRoot⟩ (readHeader new) (readHeader_eq new)
    (readCalculus outer) (readCalculus_eq outer)
    (currentCoordinates old) (currentOccurrence old)
    ⟨currentCoordinates new, currentOccurrence new
      (data index).core.revision.generate.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial⟩ operand material

theorem formAtContext_eq (operand : Operand state.root state.visit) (material : MotherArenaHigher.Material rank) :
    formAtContext state label data old outer index new face operand material =
      formClause state.calculus (label index) (data index).core.frontier.face.calculus
        ⟨(data index).core.revision.generate.NewN, (data index).core.revision.generate.NewV,
          (data index).core.revision.generate.newLivingRoot⟩ (currentCoordinates old) (currentOccurrence old)
        ⟨currentCoordinates new, currentOccurrence new
          (data index).core.revision.generate.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial⟩ operand material := by
  unfold formAtContext
  erw [formOnContexts_eq]
  rw [readCalculus_eq face]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
