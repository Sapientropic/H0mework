import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteMaterial
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Consumer
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.BandFiniteWriteback
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalRieszSource OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson.Ward
namespace M
export BandFiniteMaterial (evaluatorCode evaluator_code_eval_stage)
end M
namespace B
export OriginalKBFiniteCalculation (Value Var E sourceEnvironment fixedShift)
end B
namespace C
export OriginalKCombReceiptFeedback (bSelfSourceBinding receipt selected configuration)
end C
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (actualOccurrence nextBorn next frames root visit answeredState presentation)
end S
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
 (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured (lowInitial lowProgramme)
end CF
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower
 (birthProgram generatedAction state sourcePresentation targetPresentation target_root target_next compiles successor_valid)
end Intake
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
 (relationWrite disposition relation_write_preserves)
end P
namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (updatedSeed priorSeed)
end IP
namespace PT
export SourceOperationPaidRelations (exposure prefixHistory relations_next boundary_in_inventory)
end PT
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "material" => runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half
abbrev current := C.selected observation nontrivial depth half
abbrev sourceCfg := C.configuration observation nontrivial half
abbrev initial := CF.lowInitial (current observation nontrivial half depth) (sourceCfg observation nontrivial half)
abbrev originalProgramme := CF.lowProgramme (current observation nontrivial half depth) (sourceCfg observation nontrivial half)
abbrev Frame := SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
 (Value := PairValue B.Value) (Var := B.Var) (sort := ())

/-- Every primitive is the original bSelf source datum; the evaluator AST remains complete. -/
def boundCode := (M.evaluatorCode c B.fixedShift).subst
 (C.bSelfSourceBinding observation nontrivial depth half)

def sourceCode := liftExpr (boundCode observation nontrivial half depth)

/-- The original receiver input is retained; only this additional source program is executed. -/
def sourceTrace := execution (initial observation nontrivial half depth).rawRead.environment
 (sourceCode observation nontrivial half depth)
abbrev exposure := PT.exposure (sourceTrace observation nontrivial half depth)

/-- The standard relation writer consumes the new source trace and the current complete inventory. -/
def relationWrite (frame : Frame) := P.relationWrite (exposure observation nontrivial half depth)
 (A.epoch frame) (S.actualOccurrence frame)
 (P.disposition (exposure observation nontrivial half depth) (A.epoch frame) (S.actualOccurrence frame))

def nextInventory (frame : Frame) :=
 match (originalProgramme observation nontrivial half depth).nextInventory frame with
 | none => relationWrite observation nontrivial half depth frame
 | some prior => SourceHistoryCommon.seed prior (relationWrite observation nontrivial half depth frame)

/-- Intake installs this continuation at the original root; source datum and decoder stay original. -/
def configuration : A.Programme (PhysicalValue := PairValue B.Value) (PhysicalVar := B.Var) (sort := ()) :=
 { originalProgramme observation nontrivial half depth with
   nextInventory := fun frame => some (nextInventory observation nontrivial half depth frame) }

theorem original_datum (frame : Frame) :
 (configuration observation nontrivial half depth).datum frame =
 (originalProgramme observation nontrivial half depth).datum frame := rfl

theorem original_pair_inventory (frame : Frame) :
 (configuration observation nontrivial half depth).nextPairInventory frame =
 (originalProgramme observation nontrivial half depth).nextPairInventory frame := rfl

theorem exposure_in_relation_write (frame : Frame) (event)
 (present : event ∈ (exposure observation nontrivial half depth).trace) :
 event ∈ (relationWrite observation nontrivial half depth frame).trace := by
 apply P.relation_write_preserves
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 unfold IP.priorSeed
 cases (A.epoch frame).inventory with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_left _ _ _).1 _ present

theorem next_exposure (frame : Frame) (event)
 (present : event ∈ (exposure observation nontrivial half depth).trace) :
 event ∈ (nextInventory observation nontrivial half depth frame).trace := by
 unfold nextInventory
 cases (originalProgramme observation nontrivial half depth).nextInventory frame with
 | none => exact exposure_in_relation_write observation nontrivial half depth frame event present
 | some prior =>
   exact (SourceHistoryCommon.parallel_right _ _ _).1 _
    (exposure_in_relation_write observation nontrivial half depth frame event present)

theorem next_inherited (frame : Frame) (prior)
 (actual : (originalProgramme observation nontrivial half depth).nextInventory frame = some prior) (event)
 (present : event ∈ prior.trace) :
 event ∈ (nextInventory observation nontrivial half depth frame).trace := by
 unfold nextInventory
 rw [actual]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ present

abbrev admission := Intake.generatedAction (current observation nontrivial half depth)
 (sourceCfg observation nontrivial half) (configuration observation nontrivial half depth)
abbrev state := Intake.state (current observation nontrivial half depth)
 (sourceCfg observation nontrivial half) (configuration observation nontrivial half depth)

/-- The continuation is installed by the original root and exact current, not by a replacement root. -/
theorem original_source_root : (state observation nontrivial half depth).root =
 (S.root (current observation nontrivial half depth) (sourceCfg observation nontrivial half)) := rfl

theorem original_source_visit : (state observation nontrivial half depth).visit =
 S.visit (current observation nontrivial half depth) (sourceCfg observation nontrivial half) := rfl

theorem original_source_occurrence :
 (state observation nontrivial half depth).root.emitted (state observation nontrivial half depth).visit.current =
 (S.root (current observation nontrivial half depth) (sourceCfg observation nontrivial half)).emitted
  (S.visit (current observation nontrivial half depth) (sourceCfg observation nontrivial half)).current := rfl

theorem source_compiles : type_of% (Intake.compiles (current observation nontrivial half depth)
 (sourceCfg observation nontrivial half) (configuration observation nontrivial half depth)) := Intake.compiles _ _ _

theorem source_whole : type_of% (admission observation nontrivial half depth).target.firstDestination_heq :=
 (admission observation nontrivial half depth).target.firstDestination_heq

theorem source_next : type_of% (Intake.target_next (current observation nontrivial half depth)
 (sourceCfg observation nontrivial half) (configuration observation nontrivial half depth)
 (SourceGeneratedInquiryReceiptAction.sourceEvent (current observation nontrivial half depth)
   (sourceCfg observation nontrivial half))) := Intake.target_next _ _ _ _

theorem source_successor_valid : type_of% (Intake.successor_valid (current observation nontrivial half depth)
 (sourceCfg observation nontrivial half) (configuration observation nontrivial half depth)) := Intake.successor_valid _ _ _

abbrev selected := Complete.atReceipt (configuration observation nontrivial half depth)
 (initial observation nontrivial half depth) 0
abbrev born := S.nextBorn (selected observation nontrivial half depth) (configuration observation nontrivial half depth)
abbrev written := nextInventory observation nontrivial half depth (selected observation nontrivial half depth)

/-- Paid settlement steps retain the complete original receiver inventory. -/
theorem selected_inventory : (selected observation nontrivial half depth).inventory =
 (initial observation nontrivial half depth).inventory := by
 apply Prefix.receipt_read (configuration observation nontrivial half depth)
  (initial observation nontrivial half depth)
  (fun stage => (S.frames (initial observation nontrivial half depth)
    (configuration observation nontrivial half depth) stage).inventory)
 intro stage paid actual
 have next : S.frames (initial observation nontrivial half depth)
     (configuration observation nontrivial half depth) (stage + 1) =
   (S.frames (initial observation nontrivial half depth)
     (configuration observation nontrivial half depth) stage).mathNext := by
  change S.next _ _ = _
  unfold S.next
  rw [actual]
 exact (congrArg (fun candidate : Frame => candidate.inventory) next).trans rfl

theorem actual_compiles : type_of% (Complete.receipt_compiles (configuration observation nontrivial half depth)
 (initial observation nontrivial half depth) 0) := Complete.receipt_compiles _ _ _

theorem actual_next : type_of% (Complete.receipt_next (configuration observation nontrivial half depth)
 (initial observation nontrivial half depth) 0) := Complete.receipt_next _ _ _

theorem born_inventory : (born observation nontrivial half depth).inventory =
 some (written observation nontrivial half depth) := rfl

abbrev sourceHistory := PT.prefixHistory
 (RootedAccountedUnfolding.zero (S.actualOccurrence (current observation nontrivial half depth)))
 (exposure observation nontrivial half depth)
abbrev writtenHistory := PT.prefixHistory
 (RootedAccountedUnfolding.zero (S.actualOccurrence (born observation nontrivial half depth)))
 (written observation nontrivial half depth)

theorem source_relations_written :
 (sourceHistory observation nontrivial half depth).relationClosure ≤
 (writtenHistory observation nontrivial half depth).relationClosure :=
 PT.relations_next _ _ _ _ (next_exposure observation nontrivial half depth _)

theorem source_relations_born_kernel (word : (sourceHistory observation nontrivial half depth).relationClosure) :
 (writtenHistory observation nontrivial half depth).completionProjection
  ((Submodule.inclusion (writtenHistory observation nontrivial half depth).relationClosure_le_generatorClosure)
    ⟨word.val, source_relations_written observation nontrivial half depth word.property⟩) = 0 :=
 (Submodule.Quotient.mk_eq_zero _).2
  (source_relations_written observation nontrivial half depth word.property)

abbrev boundaryWord := relationMap (R := ℤ) (initial observation nontrivial half depth).rawRead.environment
 (sourceTrace observation nontrivial half depth).relationWords

theorem actual_boundary_kernel : type_of% (source_relations_born_kernel observation nontrivial half depth
 ⟨boundaryWord observation nontrivial half depth,
 PT.boundary_in_inventory (RootedAccountedUnfolding.zero (S.actualOccurrence (current observation nontrivial half depth)))
  (sourceTrace observation nontrivial half depth)⟩) := source_relations_born_kernel _ _ _ _ _

/-- The original scalar endpoint is consumed only after the full source program is executed. -/
theorem original_evaluator_value :
 (M.evaluatorCode c B.fixedShift).eval (material).1.environment =
 -(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual • ConstantDual.seed := by
 rw [(OriginalKCoefficientBSelfCalculation.MaterialConsumer.installed_source_raw observation nontrivial half depth).1]
 rw [M.evaluator_code_eval_stage c B.fixedShift OriginalKCoefficientBSelfCalculation.MaterialConsumer.fixed_nonnegative]
 rw [(OriginalKCoefficientBSelfCalculation.MaterialConsumer.installed_receipt_source observation nontrivial half).2]
 apply congrArg (fun scalar : ℂ => scalar • ConstantDual.seed)
 exact (OriginalRieszFinitePairing.fixed_residual_source c observation.mathlibZero).symm

private theorem bound_code_value (env : Env B.Value B.Var) :
 (boundCode observation nontrivial half depth).eval env =
 (M.evaluatorCode c B.fixedShift).eval (material).1.environment := by
 unfold boundCode
 rw [Expr.eval_subst]
 rfl

private theorem bound_code_effect (env delta : Env B.Value B.Var) :
 (boundCode observation nontrivial half depth).effect env delta = 0 := by
 unfold boundCode
 rw [Expr.effect_subst]
 change (M.evaluatorCode c B.fixedShift).effect (material).1.environment 0 = 0
 exact Expr.effect_zero _ _

/-- This is the actual executed endpoint, read from the generated AST after its source binding. -/
theorem source_code_value :
 (sourceCode observation nontrivial half depth).eval
  (initial observation nontrivial half depth).rawRead.environment =
 (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual • ConstantDual.seed, 0) := by
 let old : Env B.Value B.Var := fun sort name =>
  ((initial observation nontrivial half depth).rawRead.environment sort name).1
 let delta : Env B.Value B.Var := fun sort name =>
  ((initial observation nontrivial half depth).rawRead.environment sort name).2
 have environment : (initial observation nontrivial half depth).rawRead.environment =
   pairEnvironment old delta := rfl
 change (liftExpr (boundCode observation nontrivial half depth)).eval _ = _
 rw [environment, eval_liftExpr, bound_code_value, bound_code_effect]
 exact congrArg (fun value : B.Value () => (value, (0 : B.Value ())))
  (original_evaluator_value observation nontrivial half depth)

abbrev residualBoundary :=
 Finsupp.single (sourceCode observation nontrivial half depth) (1 : ℤ) -
 Finsupp.single (.const
  (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual • ConstantDual.seed,
   (0 : B.Value ()))) 1

theorem actual_source_boundary : boundaryWord observation nontrivial half depth =
 residualBoundary observation nontrivial half depth := by
 change relationMap (R := ℤ) _ (sourceTrace observation nontrivial half depth).relationWords = _
 rw [(sourceTrace observation nontrivial half depth).relation_boundary]
 change Finsupp.single (sourceCode observation nontrivial half depth) (1 : ℤ) -
  Finsupp.single (.const ((sourceCode observation nontrivial half depth).eval
   (initial observation nontrivial half depth).rawRead.environment)) 1 = _
 rw [source_code_value]

theorem residual_boundary_written : residualBoundary observation nontrivial half depth ∈
 (writtenHistory observation nontrivial half depth).relationClosure := by
 rw [← actual_source_boundary]
 exact source_relations_written observation nontrivial half depth
  (PT.boundary_in_inventory
   (RootedAccountedUnfolding.zero (S.actualOccurrence (current observation nontrivial half depth)))
   (sourceTrace observation nontrivial half depth))

/-- The original fixed residual equation is now a relation in the actual born completion. -/
theorem actual_residual_equation :
 (writtenHistory observation nontrivial half depth).completionProjection
  ((Submodule.inclusion (writtenHistory observation nontrivial half depth).relationClosure_le_generatorClosure)
   ⟨residualBoundary observation nontrivial half depth,
    residual_boundary_written observation nontrivial half depth⟩) = 0 :=
 (Submodule.Quotient.mk_eq_zero _).2 (residual_boundary_written observation nontrivial half depth)

/-- A receiver consumes the actual source admission, selected next, written boundary and original residual. -/
def consume_written_boundary {Result : Sort _}
 (consumer :
  type_of% (actual_residual_equation observation nontrivial half depth) →
  type_of% (source_code_value observation nontrivial half depth) →
  type_of% (source_whole observation nontrivial half depth) →
  type_of% (source_successor_valid observation nontrivial half depth) →
  type_of% (actual_compiles observation nontrivial half depth) →
  type_of% (actual_next observation nontrivial half depth) → Result) : Result :=
 consumer (actual_residual_equation observation nontrivial half depth)
  (source_code_value observation nontrivial half depth)
  (source_whole observation nontrivial half depth)
  (source_successor_valid observation nontrivial half depth)
  (actual_compiles observation nontrivial half depth) (actual_next observation nontrivial half depth)

end OriginalKPairedBEulerJunctionSource.BandFiniteWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
