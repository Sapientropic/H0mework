import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Whole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Budget
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKRawDualFeedbackSourceAction
open OriginalKMaterialExpandedDualSourceAction
open scoped InnerProductSpace
local instance priceGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance priceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def sourceExprAt (grade : Nat) := @Expr Unit (L.Value (PairValue C.Value) grade) C.Var (L.groups (PairValue C.Value) grade) ()
def sourceEnvironmentAt (grade : Nat) := Env (L.Value (PairValue C.Value) grade) C.Var
def sourceValueAt (grade : Nat) := L.Value (PairValue C.Value) grade ()

private theorem source_grade_eval {oldGrade newGrade : Nat} (same : oldGrade=newGrade)
 (code : sourceExprAt oldGrade) (environment : sourceEnvironmentAt newGrade) :
 (cast (congrArg sourceExprAt same) code).eval environment=
 cast (congrArg sourceValueAt same) (code.eval (cast (congrArg sourceEnvironmentAt same.symm) environment)) := by
 cases same
 rfl

private theorem source_grade_environment {oldGrade newGrade : Nat} (same : oldGrade=newGrade)
 (environment : sourceEnvironmentAt oldGrade) :
 (cast (congrArg sourceEnvironmentAt same) environment) () ()=
 cast (congrArg sourceValueAt same) (environment () ()) := by
 cases same
 rfl

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance nestedPriceGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target

/-- This value is transported only through the original packet's exact grade proof; the source quantity itself is never recognized by equality. -/
def actualSourceBeforeValue : Prior.Branches :=
 CF.collapseValue packet.1 (cast (congrArg sourceValueAt (source_init_born_grade t factory packet))
  (SlotSource.physicalEnvironment (sourceNextFrame t factory packet)
   (SlotSource.Shared.actualOccurrence (sourceNextFrame t factory packet)) () ()))

def actualSourceAfterValue (bornCurrent)
 (occurrence : (actualNextSourceFrame t factory packet).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent) : Prior.Branches :=
 CF.collapseValue packet.1 (cast (congrArg sourceValueAt (source_init_born_grade t factory packet))
  ((actualNextSourceFrame t factory packet).environment occurrence () ()))

/-- Real whole/current environment drives the literal successor and all raw feet, before any scalar fee is read. -/
theorem actual_whole_source_raw_successor (bornCurrent)
 (occurrence : (actualNextSourceFrame t factory packet).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent) :
 actualSourceAfterValue t factory packet bornCurrent occurrence=sourceSlotNext (actualSourceBeforeValue t factory packet) := by
 unfold actualSourceAfterValue
 rw [actual_whole_source_environment]
 let before := SlotSource.physicalEnvironment (sourceNextFrame t factory packet)
  (SlotSource.Shared.actualOccurrence (sourceNextFrame t factory packet))
 change CF.collapseValue packet.1 (cast (congrArg sourceValueAt (source_init_born_grade t factory packet))
  ((actualNestedSourceBinding t factory packet () ()).eval before))=_
 unfold actualNestedSourceBinding
 have transported := source_grade_eval (source_init_born_grade t factory packet).symm
  (CF.codeAt sourceNextSlotsCode packet.1) before
 rw [transported]
 simp only [cast_cast,cast_eq]
 rw [CF.code_base_value,source_next_code_read]
 change sourceSlotNext (CF.collapseValue packet.1
  ((cast (congrArg sourceEnvironmentAt (source_init_born_grade t factory packet)) before) () ()))=_
 rw [source_grade_environment]
 · rfl
 · exact source_init_born_grade t factory packet

/-- The complete original raw value is conserved by this actual whole update; finite stock and tail stay separate. -/
theorem actual_whole_source_raw_fee (test : BurnolQuarterMeanZeroCarrier) (bornCurrent)
 (occurrence : (actualNextSourceFrame t factory packet).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent) :
 let before:=sourceSlotsRead (actualSourceBeforeValue t factory packet)
 let after:=sourceSlotsRead (actualSourceAfterValue t factory packet bornCurrent occurrence)
 inner ℂ (before.1.1+before.2.1) test=inner ℂ after.1.1 test+inner ℂ after.2.1 test ∧
 inner ℂ (before.1.2+before.2.2) test=inner ℂ after.1.2 test+inner ℂ after.2.2 test := by
 dsimp only
 rw [actual_whole_source_raw_successor]
 unfold sourceSlotNext
 rw [source_slots_recover_raw]
 have same:=source_feedback_whole_conserved (sourceSlotsRead (actualSourceBeforeValue t factory packet))
 constructor
 · rw [←same.1,inner_add_left]
 · rw [←same.2,inner_add_left]

/-- The source law supplies this quantitative decrease only for its own raw tail, without a physical projection margin or numerical runtime debit. -/
theorem actual_whole_source_tail_bound (bornCurrent)
 (occurrence : (actualNextSourceFrame t factory packet).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent) :
 let before:=sourceSlotsRead (actualSourceBeforeValue t factory packet)
 let after:=sourceSlotsRead (actualSourceAfterValue t factory packet bornCurrent occurrence)
 ‖after.2.1‖≤(1/2:ℝ)*‖before.2.1‖ ∧ ‖after.2.2‖≤(1/2:ℝ)*‖before.2.2‖ := by
 dsimp only
 rw [actual_whole_source_raw_successor]
 unfold sourceSlotNext
 rw [source_slots_recover_raw]
 constructor
 · exact le_trans (plusFeedback.le_opNorm _) (mul_le_mul_of_nonneg_right (source_feedback_norm).1 (norm_nonneg _))
 · exact le_trans (minusFeedback.le_opNorm _) (mul_le_mul_of_nonneg_right (source_feedback_norm).2 (norm_nonneg _))
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
