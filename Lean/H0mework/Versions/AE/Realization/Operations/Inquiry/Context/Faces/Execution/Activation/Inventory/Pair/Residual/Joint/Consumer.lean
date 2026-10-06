import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
theorem kernel_word_read (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    (history seed frame occurrence).completionProjection (kernelWord seed frame occurrence sound coordinate) =
      coordinate.coordinate.val := Classical.choose_spec
    (Submodule.Quotient.mk_surjective (history seed frame occurrence).relationInGeneratorClosure coordinate.coordinate.val)

theorem query_word_read (word : Formal ℤ (PairValue PhysicalValue) PhysicalVar sort) :
    (face seed frame occurrence).freeEvaluation word =
      evaluation (R:=ℤ) (raw seed frame occurrence).environment word := by
  classical
  induction word using Finsupp.induction with
  | zero => exact (face seed frame occurrence).freeEvaluation.map_zero
  | @single_add expression integer rest absent nonzero previous =>
      rw [map_add,map_add,freeEvaluation_single,previous]
      rw [evaluation,Finsupp.linearCombination_single]
      rfl

theorem written_inventory_preserves (selected : ResidualDispositionOutcome (face seed frame occurrence)) :
    ∀ event ∈ (pairInventory seed frame occurrence).trace,
      event ∈ (writtenInventory seed frame occurrence selected).trace := by
  cases selected with
  | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => exact fun _ belongs => belongs
  | kernelResidual _ _ _ => exact (SourceHistoryCommon.parallel_left _ _ _).1

theorem complete_written_preserves :
    ∀ event ∈ (pairInventory seed frame occurrence).trace,
      event ∈ (completeWrittenInventory seed frame occurrence).trace := by
  intro event belongs
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event (written_inventory_preserves seed frame occurrence _ event belongs)

theorem complete_query_trace :
    ∀ event ∈ (SourceOperationPaidRelations.exposure (queryResult seed frame occurrence).2.1.2).trace,
      event ∈ (completeWrittenInventory seed frame occurrence).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1

def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Shared.base frame).root.source.base (component seed (epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.baseRoot frame (configuration seed)).source.base
    (Shared.queryLaw (epoch frame) (configuration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.queryRoot frame (configuration seed)).source.base
    (Shared.resultLaw (epoch frame) (configuration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.resultRoot frame (configuration seed)).source.base
    (Shared.consumerLaw (epoch frame) (configuration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.consumerRoot frame (configuration seed)).source.base
    (Shared.compilationLaw (epoch frame) (configuration seed)))
def materialFace : SourceNativeRootSemanticFaceAt (Shared.root frame (configuration seed)) (Shared.visit frame (configuration seed)) where
  projection := (installation seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem actual_query : (Shared.query frame (configuration seed)).raw =
    (materialFace seed frame).rootRead.2.2.2.2.1 := rfl

theorem original_material : (materialFace seed frame).rootRead.1 =
    Residual.material seed (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem actual_disposition : (materialFace seed frame).rootRead.2.2.2.1 =
    disposition seed (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem actual_trace : HEq (Shared.resultFace frame (configuration seed)).rootRead.2.1.2
    (queryResult seed (epoch frame) (Shared.actualOccurrence frame)).2.1.2 := by
  exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace
    (Shared.baseRoot frame (configuration seed)).toAuthoritativeRoot (Shared.visit frame (configuration seed)).current
    (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot (Shared.visit frame (configuration seed)).current
    (queryReader seed (epoch frame) (Shared.actualOccurrence frame))

theorem actual_value : (Shared.resultFace frame (configuration seed)).rootRead.2.2.1 =
    ((materialFace seed frame).rootRead.2.2.2.2.1.expression).eval
      (materialFace seed frame).rootRead.2.2.2.2.1.environment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _

theorem actual_cost : (Shared.resultFace frame (configuration seed)).rootRead.2.1.2.length =
    remaining (materialFace seed frame).rootRead.2.2.2.2.1.expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _

theorem actual_born_inventory : (Shared.nextBorn frame (configuration seed)).pairInventory =
    some (materialFace seed frame).rootRead.2.2.2.2.2 := rfl

theorem all_actual_trace_born :
    ∀ event ∈ (SourceOperationPaidRelations.exposure
      (Shared.resultFace frame (configuration seed)).rootRead.2.1.2).trace,
      event ∈ (materialFace seed frame).rootRead.2.2.2.2.2.trace := by
  have exposure : SourceOperationPaidRelations.exposure (Shared.resultFace frame (configuration seed)).rootRead.2.1.2 =
      SourceOperationPaidRelations.exposure (queryResult seed (epoch frame) (Shared.actualOccurrence frame)).2.1.2 := by
    exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
      (Shared.baseRoot frame (configuration seed)).toAuthoritativeRoot (Shared.visit frame (configuration seed)).current
      (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot (Shared.visit frame (configuration seed)).current
      (queryReader seed (epoch frame) (Shared.actualOccurrence frame))
  rw [exposure]
  exact complete_query_trace seed (epoch frame) (Shared.actualOccurrence frame)

theorem kernel_word_value (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    evaluation (R:=ℤ) (raw seed frame occurrence).environment
      (kernelWord seed frame occurrence sound coordinate).val = 0 := by
  have read := congrArg ((face seed frame occurrence).completionEvaluation sound)
    (kernel_word_read seed frame occurrence sound coordinate)
  change (face seed frame occurrence).freeEvaluation (kernelWord seed frame occurrence sound coordinate).val =
      (face seed frame occurrence).completionEvaluation sound coordinate.coordinate.val at read
  exact (query_word_read seed frame occurrence _).symm.trans (read.trans coordinate.maps_to_zero)

theorem coverage_query_value (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedCoverageResidualCoordinateAt (face seed frame occurrence) sound)
    (obstruction : GeneratedCoverageResidualObstructionAt (face seed frame occurrence) sound) :
    (queryRaw seed frame occurrence (.coverageResidual sound obstruction coordinate)).expression.eval
      (queryRaw seed frame occurrence (.coverageResidual sound obstruction coordinate)).environment = coordinate.representative := rfl

abbrev event := (Shared.root frame (configuration seed)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (Shared.visit frame (configuration seed))
theorem whole_first_write : type_of% ((Shared.targetAt frame (configuration seed) (event seed frame)).firstDestination_heq) :=
  (Shared.targetAt frame (configuration seed) (event seed frame)).firstDestination_heq

theorem literal_next : type_of% ((Shared.targetAt frame (configuration seed) (event seed frame)).targetAnswerAndNext_next_eq) :=
  (Shared.targetAt frame (configuration seed) (event seed frame)).targetAnswerAndNext_next_eq
theorem independent_updated_inverse (increment : Env (PairValue PhysicalValue) PhysicalVar) :
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.updated_inverse_fibre (R:=ℤ)
      (Shared.baseRoot frame (configuration seed)).toAuthoritativeRoot (Shared.visit frame (configuration seed)).current
      (fun _ => (Shared.query frame (configuration seed)).raw) increment) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.updated_inverse_fibre (R:=ℤ) _ _ _ increment

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
