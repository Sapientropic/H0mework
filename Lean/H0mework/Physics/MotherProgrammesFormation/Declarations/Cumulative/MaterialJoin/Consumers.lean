import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MaterialJoin.Mixed
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Joint
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.AnswerFormation
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Header

/-! Full existing factory outputs are consumed on the actual restricted
merged material. The original successful output is never an input to join. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMaterialJoin.Mixed
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
noncomputable section
universe v
variable {High Low : Type} (high : High → Ordinal.{3}) (low : Low → Ordinal.{0})
    (highMaterials : (index : High) → MotherReceiptHigher.Material (high index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index))

/-- This getter executes the existing consumer on the merged material's
actual high readback. Original availability only transports its proof. -/
def getHigh {Output : Type v} (index : High)
    (consumer : MotherReceiptHigher.Material (high index) → Option Output)
    (available : (consumer (highMaterials index)).isSome) : Output :=
  (consumer (restrictHigh high low index (combine high low highMaterials lowMaterials))).get
    (by rw [restrictHigh_combine]; exact available)

theorem getHigh_eq {Output : Type v} (index : High)
    (consumer : MotherReceiptHigher.Material (high index) → Option Output)
    (available : (consumer (highMaterials index)).isSome) :
    getHigh high low highMaterials lowMaterials index consumer available = (consumer (highMaterials index)).get available := by
  simp only [getHigh, restrictHigh_combine]

def getLow {Output : Type v} (index : Low)
    (consumer : MotherArenaHigher.Material (low index) → Option Output)
    (available : (consumer (lowMaterials index)).isSome) : Output :=
  (consumer (restrictLow high low index (combine high low highMaterials lowMaterials))).get
    (by rw [restrictLow_combine]; exact available)

theorem getLow_eq {Output : Type v} (index : Low)
    (consumer : MotherArenaHigher.Material (low index) → Option Output)
    (available : (consumer (lowMaterials index)).isSome) :
    getLow high low highMaterials lowMaterials index consumer available = (consumer (lowMaterials index)).get available := by
  simp only [getLow, restrictLow_combine]

theorem receipt_output_readback (index : High) :
    MotherReceiptPayload.formJoint (restrictHigh high low index (combine high low highMaterials lowMaterials)) =
      MotherReceiptPayload.formJoint (highMaterials index) :=
  congrArg MotherReceiptPayload.formJoint (restrictHigh_combine high low highMaterials lowMaterials index)

theorem theory_output_readback (index : Low) :
    MotherArenaTheory.formTheory (restrictLow high low index (combine high low highMaterials lowMaterials)) =
      MotherArenaTheory.formTheory (lowMaterials index) :=
  congrArg MotherArenaTheory.formTheory (restrictLow_combine high low highMaterials lowMaterials index)

theorem living_source_output_readback (index : Low) :
    MotherHandoffSource.formJoint (restrictLow high low index (combine high low highMaterials lowMaterials)) =
      MotherHandoffSource.formJoint (lowMaterials index) :=
  congrArg MotherHandoffSource.formJoint (restrictLow_combine high low highMaterials lowMaterials index)

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)

theorem answer_output_readback (index : Low) (Query : Type)
    (queryAddress : Query ↪ MotherArenaHigher.Base (low index))
    (operandAddress : MotherInquiryAnswerClause.Operand root visit ↪ MotherArenaHigher.Base (low index)) :
    MotherInquiryAnswerClause.formInquiry root visit calculus Query queryAddress operandAddress
      (restrictLow high low index (combine high low highMaterials lowMaterials)) =
      MotherInquiryAnswerClause.formInquiry root visit calculus Query queryAddress operandAddress (lowMaterials index) :=
  congrArg (MotherInquiryAnswerClause.formInquiry root visit calculus Query queryAddress operandAddress)
    (restrictLow_combine high low highMaterials lowMaterials index)

variable {oldWorld : SourceNativeAuthoritativeRootClosure N V}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {oldTheory : TheoryState N} {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure}
    {NewN : WorldRelationNetwork.{0}} {NewV : ConstructiveRoot.Vocabulary.{0}}
    {newRoot : SourceNativeLivingRootClosure NewN NewV}

theorem u8_output_readback (index : Low) (header : MotherU8Revision.LivingHeader)
    (same : header = ⟨NewN, NewV, newRoot⟩)
    (oldCoordinates : MotherU8Revision.Coordinates (rank := low index) N)
    (oldOccurrence : MotherU8Revision.OldOccurrence rooted ↪ MotherArenaHigher.Base (low index))
    (coordinates : MotherU8Revision.HeaderCoordinates (low index) ⟨NewN, NewV, newRoot⟩) :
    MotherU8Revision.formOnHeader header same oldCoordinates oldOccurrence coordinates
      (restrictLow high low index (combine high low highMaterials lowMaterials)) =
      MotherU8Revision.formOnHeader header same oldCoordinates oldOccurrence coordinates (lowMaterials index) :=
  congrArg (MotherU8Revision.formOnHeader header same oldCoordinates oldOccurrence coordinates)
    (restrictLow_combine high low highMaterials lowMaterials index)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMaterialJoin.Mixed
