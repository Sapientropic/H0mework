import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement
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

def materialFace : SourceNativeRootSemanticFaceAt (Shared.root frame (programme seed))
    (Shared.visit frame (programme seed)) where
  projection := (installation seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem query_inventory : (Shared.query frame (programme seed)).raw =
    (materialFace seed frame).rootRead.2.2.2.2.2.1 := rfl

theorem actual_disposition : (materialFace seed frame).rootRead.2.2.2.1 =
    disposition seed (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem actual_updated_seed : (materialFace seed frame).rootRead.2.1 =
    updatedSeed seed (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem prior_seed_preserved : ∀ atom ∈ (priorSeed seed (epoch frame)).trace,
    atom ∈ (materialFace seed frame).rootRead.2.1.trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1

theorem supplied_seed_preserved : ∀ atom ∈ seed.trace, atom ∈ (materialFace seed frame).rootRead.2.1.trace := by
  intro atom belongs
  apply prior_seed_preserved seed frame
  unfold priorSeed
  change atom ∈ (match frame.inventory with | none => seed | some carried => SourceHistoryCommon.seed seed carried).trace
  cases frame.inventory with
  | none => exact belongs
  | some carried => exact (SourceHistoryCommon.parallel_left _ _ _).1 atom belongs

theorem actual_word : (materialFace seed frame).rootRead.2.2.2.2.1 =
    residualWord seed (epoch frame) (Shared.actualOccurrence frame)
      (disposition seed (epoch frame) (Shared.actualOccurrence frame)) := rfl


theorem raw_value : (raw seed frame occurrence).expression.eval (raw seed frame occurrence).environment =
    (evaluation (R:=ℤ) (physical frame occurrence).raw.environment
       (residualWord seed frame occurrence (disposition seed frame occurrence)),
     effectEvaluator (R:=ℤ) (physical frame occurrence).raw.environment
       ((physical frame occurrence).nextRaw.environment - (physical frame occurrence).raw.environment)
       (residualWord seed frame occurrence (disposition seed frame occurrence))) := by
  rw [raw, eval_liftExpr, SourceOperationExecution.Coefficients.expression_eval,
    SourceOperationExecution.Coefficients.expression_effect]

theorem query_value : (Shared.resultFace frame (programme seed)).rootRead.2.2.1 =
    (evaluation (R:=ℤ) (physical (epoch frame) (Shared.actualOccurrence frame)).raw.environment
       (residualWord seed (epoch frame) (Shared.actualOccurrence frame)
         (disposition seed (epoch frame) (Shared.actualOccurrence frame))),
     effectEvaluator (R:=ℤ) (physical (epoch frame) (Shared.actualOccurrence frame)).raw.environment
       ((physical (epoch frame) (Shared.actualOccurrence frame)).nextRaw.environment -
         (physical (epoch frame) (Shared.actualOccurrence frame)).raw.environment)
       (residualWord seed (epoch frame) (Shared.actualOccurrence frame)
         (disposition seed (epoch frame) (Shared.actualOccurrence frame)))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    (raw_value seed (epoch frame) (Shared.actualOccurrence frame))

theorem query_cost : (Shared.resultFace frame (programme seed)).rootRead.2.1.2.length =
    SourceOperationExecution.Coefficients.cost
      (residualWord seed (epoch frame) (Shared.actualOccurrence frame)
        (disposition seed (epoch frame) (Shared.actualOccurrence frame))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
    (SourceOperationExecution.Coefficients.lifted_remaining _)

theorem kernel_word_read (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    (history seed frame occurrence).completionProjection (kernelWord seed frame occurrence sound coordinate) =
      coordinate.coordinate.val := Classical.choose_spec
    (Submodule.Quotient.mk_surjective (history seed frame occurrence).relationInGeneratorClosure coordinate.coordinate.val)

theorem kernel_word_value (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    evaluation (R:=ℤ) (physical frame occurrence).raw.environment
      (kernelWord seed frame occurrence sound coordinate).val = 0 := by
  have generated := congrArg ((face seed frame occurrence).completionEvaluation sound)
    (kernel_word_read seed frame occurrence sound coordinate)
  change (face seed frame occurrence).freeEvaluation (kernelWord seed frame occurrence sound coordinate).val =
    (face seed frame occurrence).completionEvaluation sound coordinate.coordinate.val at generated
  exact generated.trans coordinate.maps_to_zero

theorem coverage_word_value (representative : PhysicalValue sort) :
    evaluation (R:=ℤ) (physical frame occurrence).raw.environment
      (Finsupp.single (.const representative) 1) = representative := by
  simp only [evaluation, Finsupp.linearCombination_single, one_smul, Expr.eval]



theorem next_inventory_from_face : (programme seed).nextInventory frame =
    some (materialFace seed frame).rootRead.2.2.2.2.2.2.2 := rfl

theorem relation_write_preserves (selected : ResidualDispositionOutcome (face seed frame occurrence)) :
    ∀ atom ∈ (updatedSeed seed frame occurrence).trace,
    atom ∈ (relationWrite seed frame occurrence selected).trace := by
  cases selected with
  | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => exact fun _ belongs => belongs
  | kernelResidual _ _ _ => exact (SourceHistoryCommon.parallel_left _ _ _).1

theorem birth_inventory_preserved : ∀ atom ∈ (materialFace seed frame).rootRead.2.1.trace,
    atom ∈ (materialFace seed (Shared.nextBorn frame (programme seed))).rootRead.2.1.trace := by
  intro atom belongs
  apply prior_seed_preserved seed _
  change atom ∈ (SourceHistoryCommon.seed seed
    (writtenSeed seed (epoch frame) (Shared.actualOccurrence frame))).trace
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  exact relation_write_preserves seed (epoch frame) (Shared.actualOccurrence frame) _ atom belongs

abbrev event := (Shared.root frame (programme seed)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (Shared.visit frame (programme seed))

theorem birth_old_inventory (projection : (Shared.root frame (programme seed)).source.base.projectionLaw.Projection) :
    type_of% ((Shared.targetAt frame (programme seed) (event seed frame)).oldOutcome_heq projection) :=
  (Shared.targetAt frame (programme seed) (event seed frame)).oldOutcome_heq projection

def bornOutcome := (Shared.targetAt frame (programme seed) (event seed frame)).targetRoot.source.base.projectionLaw.outcomeAt
  ((Shared.targetAt frame (programme seed) (event seed frame)).oldProjection (materialFace seed frame).projection)
  ((Shared.targetAt frame (programme seed) (event seed frame)).targetRoot.emitted
    (Shared.targetAt frame (programme seed) (event seed frame)).targetRoot.toAuthoritativeRoot.toRoot.initialVisit.current)

theorem born_material_read : HEq (bornOutcome seed frame)
    ((Shared.root frame (programme seed)).source.base.projectionLaw.outcomeAt
      (materialFace seed frame).projection
      ((Shared.root frame (programme seed)).emitted (Shared.visit frame (programme seed)).current)) :=
  (Shared.targetAt frame (programme seed) (event seed frame)).oldOutcome_heq (materialFace seed frame).projection

theorem birth_whole_first_write : type_of%
    ((Shared.targetAt frame (programme seed) (event seed frame)).firstDestination_heq) :=
  (Shared.targetAt frame (programme seed) (event seed frame)).firstDestination_heq

theorem birth_literal_next : type_of%
    ((Shared.targetAt frame (programme seed) (event seed frame)).targetAnswerAndNext_next_eq) :=
  (Shared.targetAt frame (programme seed) (event seed frame)).targetAnswerAndNext_next_eq

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
