import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarInventoryLift
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Shared.base frame).root.source.base (component seed (epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.baseRoot frame (programme seed)).source.base
    (Shared.queryLaw (epoch frame) (programme seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.queryRoot frame (programme seed)).source.base
    (Shared.resultLaw (epoch frame) (programme seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.resultRoot frame (programme seed)).source.base
    (Shared.consumerLaw (epoch frame) (programme seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.consumerRoot frame (programme seed)).source.base
    (Shared.compilationLaw (epoch frame) (programme seed)))
def materialFace : SourceNativeRootSemanticFaceAt (Shared.root frame (programme seed)) (Shared.visit frame (programme seed)) where
  projection := (installation seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem scalar_material : (materialFace seed frame).rootRead.1 =
    InventoryProgramme.material seed (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem query_material : (Shared.query frame (programme seed)).raw =
    (materialFace seed frame).rootRead.2.2.2.2.1 := rfl

theorem word_read (word : Formal ℤ PhysicalValue PhysicalVar sort) :
    (face seed frame occurrence).freeEvaluation word = updateInventory (R:=ℤ)
      (physical frame occurrence).raw.environment (delta frame occurrence) word := by
  classical
  induction word using Finsupp.induction with
  | zero => exact (face seed frame occurrence).freeEvaluation.map_zero
  | @single_add expression integer rest absent nonzero previous =>
      rw [map_add,map_add,freeEvaluation_single,previous]
      apply congrArg₂ (· + ·) ?_ rfl
      change integer • (expression.eval (physical frame occurrence).raw.environment,
        expression.effect (physical frame occurrence).raw.environment (delta frame occurrence)) = _
      apply Prod.ext
      · change integer • expression.eval (physical frame occurrence).raw.environment =
          evaluation (R:=ℤ) (physical frame occurrence).raw.environment (Finsupp.single expression integer)
        rw [evaluation,Finsupp.linearCombination_single]
      · change integer • expression.effect (physical frame occurrence).raw.environment (delta frame occurrence) =
          effectEvaluator (R:=ℤ) (physical frame occurrence).raw.environment (delta frame occurrence) (Finsupp.single expression integer)
        rw [effectEvaluator,Finsupp.linearCombination_single]


theorem scalar_projection (word : Formal ℤ PhysicalValue PhysicalVar sort) :
    ((face seed frame occurrence).freeEvaluation word).1 =
      (InventoryProgramme.face seed frame occurrence).freeEvaluation word := by
  apply (congrArg Prod.fst (word_read seed frame occurrence word)).trans
  change evaluation (R:=ℤ) (physical frame occurrence).raw.environment word =
    (InventoryProgramme.face seed frame occurrence).freeEvaluation word
  classical
  induction word using Finsupp.induction with
  | zero => exact (InventoryProgramme.face seed frame occurrence).freeEvaluation.map_zero.symm
  | @single_add expression integer rest absent nonzero previous =>
      rw [map_add,map_add,freeEvaluation_single]
      apply congrArg₂ (· + ·) ?_ previous
      rw [evaluation,Finsupp.linearCombination_single]
      rfl

theorem kernel_word_read (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    (InventoryProgramme.history seed frame occurrence).completionProjection (kernelWord seed frame occurrence sound coordinate) =
      coordinate.coordinate.val := Classical.choose_spec
    (Submodule.Quotient.mk_surjective (InventoryProgramme.history seed frame occurrence).relationInGeneratorClosure coordinate.coordinate.val)

theorem kernel_pair_zero (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    updateInventory (R:=ℤ) (physical frame occurrence).raw.environment (delta frame occurrence)
      (kernelWord seed frame occurrence sound coordinate).val = (0,0) := by
  have generated := congrArg ((face seed frame occurrence).completionEvaluation sound)
    (kernel_word_read seed frame occurrence sound coordinate)
  change (face seed frame occurrence).freeEvaluation (kernelWord seed frame occurrence sound coordinate).val =
    (face seed frame occurrence).completionEvaluation sound coordinate.coordinate.val at generated
  exact (word_read seed frame occurrence _).symm.trans (generated.trans coordinate.maps_to_zero)


theorem kernel_next_zero (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    evaluation (R:=ℤ) (physical frame occurrence).nextRaw.environment
      (kernelWord seed frame occurrence sound coordinate).val = 0 := by
  have pairZero := kernel_pair_zero seed frame occurrence sound coordinate
  have oldZero := congrArg Prod.fst pairZero
  have effectZero := congrArg Prod.snd pairZero
  have nextEnvironment : (physical frame occurrence).raw.environment + delta frame occurrence =
      (physical frame occurrence).nextRaw.environment := add_sub_cancel _ _
  rw [← nextEnvironment,evaluation_update,LinearMap.add_apply]
  exact (congrArg₂ (· + ·) oldZero effectZero).trans (zero_add _)

-- Every branch executes its actual pair word or retains its generated coverage representative.
theorem kernel_query_value (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (obstruction : GeneratedCoverageResidualObstructionAt (face seed frame occurrence) sound)
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    (queryRaw seed frame occurrence (.kernelResidual sound obstruction coordinate)).expression.eval
      (queryRaw seed frame occurrence (.kernelResidual sound obstruction coordinate)).environment = (0,0) := by
  change (liftExpr (SourceOperationExecution.Coefficients.expression
    (kernelWord seed frame occurrence sound coordinate).val)).eval
      (pairEnvironment (physical frame occurrence).raw.environment (delta frame occurrence)) = (0,0)
  rw [eval_liftExpr,SourceOperationExecution.Coefficients.expression_eval,
    SourceOperationExecution.Coefficients.expression_effect]
  exact kernel_pair_zero seed frame occurrence sound coordinate

theorem coverage_query_value (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (obstruction : GeneratedCoverageResidualObstructionAt (face seed frame occurrence) sound)
    (coordinate : GeneratedCoverageResidualCoordinateAt (face seed frame occurrence) sound) :
    (queryRaw seed frame occurrence (.coverageResidual sound obstruction coordinate)).expression.eval
      (queryRaw seed frame occurrence (.coverageResidual sound obstruction coordinate)).environment = coordinate.representative := rfl


theorem initial_seed_preserved : ∀ atom ∈ seed.trace,
    atom ∈ (materialFace seed frame).rootRead.2.1.trace := InventoryProgramme.supplied_seed_preserved seed frame

theorem query_value : (Shared.resultFace frame (programme seed)).rootRead.2.2.1 =
    (queryRaw seed (epoch frame) (Shared.actualOccurrence frame)
      (disposition seed (epoch frame) (Shared.actualOccurrence frame))).expression.eval
        (queryRaw seed (epoch frame) (Shared.actualOccurrence frame)
          (disposition seed (epoch frame) (Shared.actualOccurrence frame))).environment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _

theorem query_cost : (Shared.resultFace frame (programme seed)).rootRead.2.1.2.length =
    remaining (queryRaw seed (epoch frame) (Shared.actualOccurrence frame)
      (disposition seed (epoch frame) (Shared.actualOccurrence frame))).expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _

theorem relation_write_preserves (selected : ResidualDispositionOutcome (face seed frame occurrence)) :
    ∀ atom ∈ (updatedSeed seed frame occurrence).trace,
    atom ∈ (relationWrite seed frame occurrence selected).trace := by
  cases selected with
  | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => exact fun _ belongs => belongs
  | kernelResidual _ _ _ => exact (SourceHistoryCommon.parallel_left _ _ _).1

theorem birth_inventory_preserved : ∀ atom ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
    atom ∈ (updatedSeed seed (epoch (Shared.nextBorn frame (programme seed)))
      (Shared.actualOccurrence (Shared.nextBorn frame (programme seed)))).trace := by
  intro atom belongs
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  change atom ∈ (SourceHistoryCommon.seed seed (relationWrite seed (epoch frame) (Shared.actualOccurrence frame)
    (disposition seed (epoch frame) (Shared.actualOccurrence frame)))).trace
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  exact relation_write_preserves seed (epoch frame) (Shared.actualOccurrence frame) _ atom belongs


abbrev event := (Shared.root frame (programme seed)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (Shared.visit frame (programme seed))
theorem birth_old_inventory (projection : (Shared.root frame (programme seed)).source.base.projectionLaw.Projection) :
    type_of% ((Shared.targetAt frame (programme seed) (event seed frame)).oldOutcome_heq projection) :=
  (Shared.targetAt frame (programme seed) (event seed frame)).oldOutcome_heq projection

theorem birth_whole_first_write : type_of%
    ((Shared.targetAt frame (programme seed) (event seed frame)).firstDestination_heq) :=
  (Shared.targetAt frame (programme seed) (event seed frame)).firstDestination_heq

theorem birth_literal_next : type_of%
    ((Shared.targetAt frame (programme seed) (event seed frame)).targetAnswerAndNext_next_eq) :=
  (Shared.targetAt frame (programme seed) (event seed frame)).targetAnswerAndNext_next_eq

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
