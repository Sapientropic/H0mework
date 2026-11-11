import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.PaidNativeMethod.RelationCochain.Source
import H0mework.Versions.MF.Realization.Perfectification.Cofinal.LivingLawRootGeneratedCofinalRelationComplexKernel
import H0mework.Realization.Operations.InventoryLift.Substitution

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod.RelationCochain
attribute [local instance] SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod.zeroGroups
open CategoryTheory RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationNative
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
 (component combined material face)
namespace E
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.Elimination
 (fourFaces dual_readback)
end E
end Faces
namespace AI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
 (raw actual_environment)
end AI
namespace Old
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod (InstalledFaces)
end Old
namespace E
export UnifiedFourFace.Evaluation (Input RootEvaluation generate move generated_action generated_action_embedding generated_equation)
end E
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (liftTraceZero liftStepZero)
end WR
variable (sourceRuntime : LivingRuntimeState process)
private def inheritedFaces (frame : PhysicalFrame) :
 Old.InstalledFaces frame (Base.method sourceRuntime) (configuration sourceRuntime) := by
 let base := sourceProgramme sourceRuntime
 let actual := configuration sourceRuntime
 let method := Base.method sourceRuntime
 let installed := ((SourceNativeProjectionLaw.InstallationAt.componentCoface
  (A.optionalSourceRoot (S.base (A.epoch frame)).root (method.datum (A.epoch frame)).component).source.base
  (Faces.component (A.epoch frame) method)).trans
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
   (S.base (A.epoch frame)).root.source.base (Faces.combined (A.epoch frame) method))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (A.optionalSourceRoot (S.base (A.epoch frame)).root
    ((Base.sourceProgramme sourceRuntime).datum (A.epoch frame)).component).source.base
   (replayComponent frame)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   { (S.base (A.epoch frame)).root.source.base with projectionLaw := combined sourceRuntime frame }
   (I.stockLaw (A.epoch frame) base)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
   (I.component (A.epoch frame) base)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame actual).source.base
   (S.queryLaw (A.epoch frame) actual)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame actual).source.base
   (S.resultLaw (A.epoch frame) actual)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame actual).source.base
   (S.consumerLaw (A.epoch frame) actual)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame actual).source.base
   (S.compilationLaw (A.epoch frame) actual))
 let actualFace : SourceNativeRootSemanticFaceAt (S.root frame actual) (S.visit frame actual) :=
  { projection := installed.embed PUnit.unit, active := PUnit.unit, classifier_eq := rfl }
 exact { face := actualFace,
         packet := actualFace.rootRead,
         source_readback := HEq.rfl,
         original_face := rfl,
         reader_source := rfl,
         fourFaces := Faces.E.fourFaces (A.epoch frame) method (S.actualOccurrence frame) actualFace.rootRead,
         dual_readback := Faces.E.dual_readback (A.epoch frame) method (S.actualOccurrence frame) actualFace.rootRead }



abbrev physicalRuntime (count : Nat) := sourceRuntime.advance (11+count)

def nativeForward (count : Nat) :=
 Context.WordExecution.pairedForward SourcePhysicalContextRelationConsumer.readPaired
  (point (physicalRuntime sourceRuntime count)) (liftExpr fockOperation)

theorem native_primitive_source (count : Nat) :
 Context.WordExecution.observerEnvironment SourcePhysicalContextRelationConsumer.readPaired
  (sourceAction process (point (physicalRuntime sourceRuntime count))) =
 SourcePhysicalContextRelationConsumer.readPaired (physicalRuntime sourceRuntime count).tick.next.state :=
 (congrArg (Context.WordExecution.observerEnvironment SourcePhysicalContextRelationConsumer.readPaired)
  (sourceAction_point (physicalRuntime sourceRuntime count))).trans
  (Context.WordExecution.observerEnvironment_point SourcePhysicalContextRelationConsumer.readPaired
   (physicalRuntime sourceRuntime count).tick.next)

-- First physical source splice: same source syntax, actual current paid environment.
-- A value equation is not used to identify different execution traces.
theorem native_forward_environment (count : Nat) :
 pairEnvironment (Context.environment (PhysicalValue := PairValue OperationValue)
  (point (physicalRuntime sourceRuntime count))) 0 = actualPairEnv sourceRuntime count := by
 exact congrArg (fun env => pairEnvironment env (0 : Env W X))
  ((environment_actual sourceRuntime count).symm.trans (paid_current sourceRuntime count).symm)

private def environmentTransport {first second : Env (PairValue W) X}
 {before after : Expr (PairValue W) X s} (same : first = second)
 (paid : Trace first before after) : Trace second before after :=
 Eq.mp (congrArg (fun env => Trace env before after) same) paid

def nativeReplayAt (count : Nat) := environmentTransport
 (native_forward_environment sourceRuntime count) (nativeForward sourceRuntime count)

abbrev ReplayStock := RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) X s))
def BornContains (frame : Frame) (written : ReplayStock) : Prop :=
 ∀ event ∈ written.trace, event ∈ (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)).trace

def NextContains (frame : Frame) (written : ReplayStock) : Prop :=
 ∀ event ∈ written.trace, event ∈ (PM.completeQueryWritten 0
  (S.nextBorn frame (configuration sourceRuntime))).trace

-- This subordinate transport consumes an internally generated environment equation.
-- The public source mouth supplies neither an environment nor a containment witness.
private theorem exposure_environment {first second : Env (PairValue W) X}
 {before after : Expr (PairValue W) X s} (same : first=second) (paid : Trace first before after) :
 SourceOperationPaidRelations.exposure (environmentTransport same paid) = SourceOperationPaidRelations.exposure paid := by
 cases same
 rfl

open private transportPairEnv from
 H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.PaidNativeMethod.RelationCochain.Source

private theorem source_exposure_environment {first second : Env (PairValue W) X}
 {before after : Expr (PairValue W) X s} (same : first=second) (paid : Trace first before after) :
 SourceOperationPaidRelations.exposure (transportPairEnv same paid) = SourceOperationPaidRelations.exposure paid := by
 cases same
 rfl

def wordStock (word : Carrier process) := SourceOperationPaidRelations.exposure
 (Context.WordExecution.pairedForward SourcePhysicalContextRelationConsumer.readPaired word (liftExpr fockOperation))

private theorem replay_stock_word (frame : Frame) :
 replayStock frame = wordStock (sourceWord frame (S.actualOccurrence frame)) := by
 unfold replayStock replay
 exact source_exposure_environment _ _

private theorem source_word_actual (count : Nat) :
 sourceWord (actualFrame sourceRuntime count) (S.actualOccurrence (actualFrame sourceRuntime count)) =
 point (physicalRuntime sourceRuntime count) :=
 congrArg (fun env => env (Sum.inr PUnit.unit) PUnit.unit)
  ((paid_current sourceRuntime count).trans (environment_actual sourceRuntime count))

private theorem native_stock_eq (count : Nat) :
 SourceOperationPaidRelations.exposure (nativeReplayAt sourceRuntime count) =
 replayStock (actualFrame sourceRuntime count) :=
 (exposure_environment (native_forward_environment sourceRuntime count) (nativeForward sourceRuntime count)).trans
  ((congrArg wordStock (source_word_actual sourceRuntime count)).symm.trans
   (replay_stock_word (actualFrame sourceRuntime count)).symm)

theorem native_replay_written (count : Nat) :
 BornContains sourceRuntime (actualFrame sourceRuntime count)
  (SourceOperationPaidRelations.exposure (nativeReplayAt sourceRuntime count)) :=
 (congrArg (BornContains sourceRuntime (actualFrame sourceRuntime count)) (native_stock_eq sourceRuntime count)).mpr
  (replay_written sourceRuntime (actualFrame sourceRuntime count))

theorem native_replay_next_query (count : Nat) :
 NextContains sourceRuntime (actualFrame sourceRuntime count)
  (SourceOperationPaidRelations.exposure (nativeReplayAt sourceRuntime count)) :=
 (congrArg (NextContains sourceRuntime (actualFrame sourceRuntime count)) (native_stock_eq sourceRuntime count)).mpr
  (replay_next_query sourceRuntime (actualFrame sourceRuntime count))

def nativeSourceForward (count : Nat) :=
 WR.liftTraceZero (Context.WordExecution.embeddedTrace SourcePhysicalContextRelationConsumer.readPaired
  (sourceAction process (point (physicalRuntime sourceRuntime count)))
  (execution (Context.WordExecution.observerEnvironment SourcePhysicalContextRelationConsumer.readPaired
   (sourceAction process (point (physicalRuntime sourceRuntime count)))) (liftExpr fockOperation)))

private theorem native_source_environment (count : Nat) :
 pairEnvironment (Context.environment (PhysicalValue := PairValue OperationValue)
  (sourceAction process (point (physicalRuntime sourceRuntime count)))) 0 =
 SourceSubstitution.sourceEnvironment pairBinding (actualPairEnv sourceRuntime count) := by
 exact ((congrArg (fun word => pairEnvironment (Context.environment (PhysicalValue := PairValue OperationValue) word)
  (0 : Env W X)) (sourceAction_point (physicalRuntime sourceRuntime count))).trans
  (native_forward_environment sourceRuntime (count+1))).trans (paired_binding_square sourceRuntime count).symm

def nativeSourceAt (count : Nat) := environmentTransport
 (native_source_environment sourceRuntime count) (nativeSourceForward sourceRuntime count)

def sourceRelations (count : Nat) := (nativeSourceAt sourceRuntime count).relationWords (R := ℤ)
def sourceRelationWord (count : Nat) := relationMap (R := ℤ)
 (SourceSubstitution.sourceEnvironment pairBinding (actualPairEnv sourceRuntime count))
 (sourceRelations sourceRuntime count)

def actualComplex (count : Nat) := SourceSubstitution.complexMorphism (R := ℤ) (s := s)
 pairBinding (actualPairEnv sourceRuntime count)

def nextHistory (count : Nat) :=
 let frame := actualFrame sourceRuntime count
 let born := S.nextBorn frame (configuration sourceRuntime)
 SourceOperationPaidRelations.prefixHistory (.zero (S.actualOccurrence born))
  (PM.completeQueryWritten 0 born)

def actualBoundary (count : Nat) : (nextHistory sourceRuntime count).relationClosure :=
 ⟨relationMap (R := ℤ) (actualPairEnv sourceRuntime count)
   (nativeReplayAt sourceRuntime count).relationWords,
  SourceOperationPaidRelations.relations_next
   (.zero (S.actualOccurrence (actualFrame sourceRuntime count)))
   (SourceOperationPaidRelations.exposure (nativeReplayAt sourceRuntime count))
   (.zero (S.actualOccurrence (S.nextBorn (actualFrame sourceRuntime count) (configuration sourceRuntime))))
   (PM.completeQueryWritten 0 (S.nextBorn (actualFrame sourceRuntime count) (configuration sourceRuntime)))
   (native_replay_next_query sourceRuntime count)
   (SourceOperationPaidRelations.boundary_in_inventory _ (nativeReplayAt sourceRuntime count))⟩

theorem actual_boundary_from_source (count : Nat) :
 (actualBoundary sourceRuntime count).val =
 substitution (R := ℤ) pairBinding (sourceRelationWord sourceRuntime count) := by
 change relationMap (R := ℤ) (actualPairEnv sourceRuntime count)
  (nativeReplayAt sourceRuntime count).relationWords =
  substitution (R := ℤ) pairBinding
   (relationMap (R := ℤ) _ (nativeSourceAt sourceRuntime count).relationWords)
 rw [(nativeReplayAt sourceRuntime count).relation_boundary,
  (nativeSourceAt sourceRuntime count).relation_boundary, map_sub]
 simp only [substitution, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
 exact congrArg₂ (fun before after => Finsupp.single before (1 : ℤ)-Finsupp.single after 1)
  (SubstitutionLift.expression Context.binding SourcePhysicalCalculation.rawExpression) rfl

theorem actual_complex_boundary (count : Nat) :
 relationMap (R := ℤ) (actualPairEnv sourceRuntime count)
  ((actualComplex sourceRuntime count).τ₁.hom (sourceRelations sourceRuntime count)) =
 (actualBoundary sourceRuntime count).val :=
 (LinearMap.congr_fun (SourceSubstitution.boundary_square pairBinding (actualPairEnv sourceRuntime count))
  (sourceRelations sourceRuntime count)).trans (actual_boundary_from_source sourceRuntime count).symm

def actualCochain (count : Nat) := CofinalRelationGeneratedComplex.natComplex (nextHistory sourceRuntime count)
theorem generated_differential (count : Nat) :
 (((actualCochain sourceRuntime count).d 0 1).hom (actualBoundary sourceRuntime count)).val =
  (actualBoundary sourceRuntime count).val := by
 exact congrArg (fun delta : (actualCochain sourceRuntime count).X 0 ⟶
  (actualCochain sourceRuntime count).X 1 => (delta.hom (actualBoundary sourceRuntime count)).val)
  (CofinalRelationGeneratedComplex.natComplex_d_zero_one (nextHistory sourceRuntime count))

theorem actual_complex_differential (count : Nat) :
 (((actualCochain sourceRuntime count).d 0 1).hom (actualBoundary sourceRuntime count)).val =
 relationMap (R := ℤ) (actualPairEnv sourceRuntime count)
  ((actualComplex sourceRuntime count).τ₁.hom (sourceRelations sourceRuntime count)) :=
 (generated_differential sourceRuntime count).trans (actual_complex_boundary sourceRuntime count).symm

theorem completion_consumes_relation (count : Nat) :
 (nextHistory sourceRuntime count).completionProjection
  (((actualCochain sourceRuntime count).d 0 1).hom (actualBoundary sourceRuntime count)) = 0 :=
 CofinalRelationGeneratedComplex.completion_kills_generated_differential _ _

abbrev Packet (count : Nat) := type_of% (material (actualFrame sourceRuntime count)
 (S.actualOccurrence (actualFrame sourceRuntime count)))
abbrev SourceCarrier (count : Nat) :=
 PresentedRelationEventAt (Expr (PairValue W) X s) × Packet sourceRuntime count

def sourceUnfolding (count : Nat) := callback sourceRuntime (actualFrame sourceRuntime count)
def sourceOccurrence (count : Nat) :=
 (sourceUnfolding sourceRuntime count).map (fun event =>
  (event, (face sourceRuntime (actualFrame sourceRuntime count)).rootRead))

theorem source_occurrence_erasure (count : Nat) :
 (sourceOccurrence sourceRuntime count).map Prod.fst = sourceUnfolding sourceRuntime count := by
 unfold sourceOccurrence
 rw [RootedAccountedUnfolding.map_map]
 exact RootedAccountedUnfolding.map_id _

theorem source_occurrence_readback (count : Nat) :
 (sourceOccurrence sourceRuntime count).root.2 =
 (face sourceRuntime (actualFrame sourceRuntime count)).rootRead := by
 rw [sourceOccurrence, RootedAccountedUnfolding.root_map]

private def packetEnvironment (count : Nat) (point : SourceCarrier sourceRuntime count) :=
 pairEnvironment (N.input point.2.1.paid).environment 0
private def algebraAt (count : Nat) (point : SourceCarrier sourceRuntime count) :=
 (point, evaluation (R := ℤ) (s := s) (packetEnvironment sourceRuntime count point))
private def combinatorialAt (count : Nat) (point : SourceCarrier sourceRuntime count) :=
 (point, sourceUnfolding sourceRuntime count, point.2.2.2.1)
private def topologicalAt (count : Nat) (point : SourceCarrier sourceRuntime count) :=
 (point, nextHistory sourceRuntime count, CofinalAllPrimeTopology.TopologicalAt.generate (nextHistory sourceRuntime count))
private def logicalAt (count : Nat) (point : SourceCarrier sourceRuntime count) :=
 PProd.mk point (completion_consumes_relation sourceRuntime count)
private def relationAt (count : Nat) (point : SourceCarrier sourceRuntime count) :=
 (point, actualBoundary sourceRuntime count)
private def cochainAt (count : Nat) (point : SourceCarrier sourceRuntime count) :=
 (point, actualCochain sourceRuntime count, actualComplex sourceRuntime count)

def faceInput (count : Nat) :=
 ({ occurrence := sourceOccurrence sourceRuntime count
    algebraAt := algebraAt sourceRuntime count
    combinatorialAt := combinatorialAt sourceRuntime count
    topologicalAt := topologicalAt sourceRuntime count
    logicalAt := logicalAt sourceRuntime count
    relationAt := relationAt sourceRuntime count
    cochainAt := cochainAt sourceRuntime count
    evaluationAt := fun original => evaluation (R := ℤ) (s := s) (packetEnvironment sourceRuntime count original)
    faithfulAt := fun _ => substitution (R := ℤ) pairBinding } :
 E.Input (SourceCarrier sourceRuntime count) _ _ _ _ _ _
  (Formal ℤ (PairValue W) X s) (PairValue W s))

def faceAction (count : Nat) : SourceGeneratedScalarDifferentialResidual.Morphism
 (E.RootEvaluation (faceInput sourceRuntime (count+1))) (E.RootEvaluation (faceInput sourceRuntime count)) where
 sourceMap := substitution (R := ℤ) pairBinding
 targetMap := LinearMap.id
 commutes := by
  apply LinearMap.ext
  intro word
  change evaluation (R := ℤ) (actualPairEnv sourceRuntime (count+1)) word =
   evaluation (R := ℤ) (actualPairEnv sourceRuntime count) (substitution (R := ℤ) pairBinding word)
  rw [← paired_binding_square sourceRuntime count]
  exact (LinearMap.congr_fun (evaluation_substitution (R := ℤ) pairBinding
   (actualPairEnv sourceRuntime count)) word).symm

def coimageAction (count : Nat) := E.move (input := faceInput sourceRuntime (count+1))
 (input' := faceInput sourceRuntime count) (faceAction sourceRuntime count)

theorem actual_coimage_action (count : Nat) (word : Formal ℤ (PairValue W) X s) :
 coimageAction sourceRuntime count ((E.generate (faceInput sourceRuntime (count+1))).canonical word) =
 (E.generate (faceInput sourceRuntime count)).canonical (substitution (R := ℤ) pairBinding word) :=
 E.generated_action (faceAction sourceRuntime count) word

theorem actual_coimage_boundary (count : Nat) :
 coimageAction sourceRuntime count
  ((E.generate (faceInput sourceRuntime (count+1))).canonical (sourceRelationWord sourceRuntime count)) =
 (E.generate (faceInput sourceRuntime count)).canonical (actualBoundary sourceRuntime count).val :=
 (actual_coimage_action sourceRuntime count (sourceRelationWord sourceRuntime count)).trans
  (congrArg (E.generate (faceInput sourceRuntime count)).canonical (actual_boundary_from_source sourceRuntime count).symm)

theorem actual_coimage_differential (count : Nat) :
 (E.generate (faceInput sourceRuntime count)).embedding (coimageAction sourceRuntime count
  ((E.generate (faceInput sourceRuntime (count+1))).canonical (sourceRelationWord sourceRuntime count))) =
 evaluation (R := ℤ) (actualPairEnv sourceRuntime count)
  (((actualCochain sourceRuntime count).d 0 1).hom (actualBoundary sourceRuntime count)).val := by
 have moved := congrArg (E.generate (faceInput sourceRuntime count)).embedding
  (actual_coimage_boundary sourceRuntime count)
 have read := LinearMap.congr_fun (E.generated_equation (faceInput sourceRuntime count))
  (actualBoundary sourceRuntime count).val
 exact moved.trans (read.trans (congrArg (evaluation (R := ℤ) (actualPairEnv sourceRuntime count))
  (generated_differential sourceRuntime count).symm))

open private paidQueryStock completePairOutput preserves_right from
 H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.PaidNativeMethod.Source

private theorem original_paid_written (frame : Frame) :
 BornContains sourceRuntime frame
  (SourceOperationPaidRelations.exposure (R.actualMaterial frame (Base.method sourceRuntime)).state.2) := by
 have carried := PM.Generic.birth_keeps_callback frame (sourceProgramme sourceRuntime)
  (callback sourceRuntime frame) rfl
 intro event present
 apply carried event
 change event ∈ (RootedAccountedUnfolding.parallelAt _ (completePairOutput sourceRuntime frame) (replayStock frame)).trace
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event
  (preserves_right _ _ event ((SourceHistoryCommon.parallel_left _ _ _).1 event present))

private theorem born_stock_consumed (frame : Frame) :
 ∀ event ∈ (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)).trace,
 event ∈ (PM.completeQueryWritten 0 (S.nextBorn frame (configuration sourceRuntime))).trace := by
 let born := S.nextBorn frame (configuration sourceRuntime)
 have pairEq : (A.epoch born).pairInventory = some (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)) :=
  PM.Generic.birth_stock frame (sourceProgramme sourceRuntime)
 intro event present
 apply Joint.complete_written_preserves (I.seed born) (A.epoch born) (S.actualOccurrence born) event
 unfold Res.pairInventory Res.priorPairInventory
 rw [pairEq]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_left _ _ _).1 event present)

private theorem original_paid_consumed (frame : Frame) :
 ∀ event ∈ (SourceOperationPaidRelations.exposure (R.actualMaterial frame (Base.method sourceRuntime)).state.2).trace,
 event ∈ (PM.completeQueryWritten 0 (S.nextBorn frame (configuration sourceRuntime))).trace :=
 fun event present => born_stock_consumed sourceRuntime frame event (original_paid_written sourceRuntime frame event present)

open private PhysicalReadback physical_readback from
 H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.PaidNativeMethod.Consumer

def activeWord (count : Nat) :=
 paidEnvironment (actualFrame sourceRuntime count) (S.actualOccurrence (actualFrame sourceRuntime count))
  (Sum.inr PUnit.unit) PUnit.unit

theorem word_actual (count : Nat) : activeWord sourceRuntime count = point (physicalRuntime sourceRuntime count) :=
 congrArg (fun env => env (Sum.inr PUnit.unit) PUnit.unit)
  ((paid_current sourceRuntime count).trans (environment_actual sourceRuntime count))

theorem word_forward (count : Nat) :
 sourceAction process (activeWord sourceRuntime count) = activeWord sourceRuntime (count+1) := by
 rw [word_actual, word_actual]
 exact sourceAction_point (physicalRuntime sourceRuntime count)

theorem word_segment (start fuel : Nat) :
 (fun word : Carrier process => sourceAction process word)^[fuel] (activeWord sourceRuntime start) =
 activeWord sourceRuntime (start+fuel) := by
 induction fuel with
 | zero => rfl
 | succ fuel prior =>
  rw [Function.iterate_succ_apply', prior]
  simpa only [Nat.add_assoc] using word_forward sourceRuntime (start+fuel)

private theorem source_value (frame : Frame) :
 (R.actionResultAt frame (configuration sourceRuntime) (S.actualOccurrence frame)).2.2.1 =
 (Base.fullNativeExpression.eval frame.activeEnvironment,0) := by
 have raw : R.actionReader frame (configuration sourceRuntime) (S.actualOccurrence frame) =
  AI.raw 0 (A.epoch frame) Base.sourceCode (S.actualOccurrence frame) := rfl
 have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (S.baseRoot frame (configuration sourceRuntime)).toAuthoritativeRoot
  (R.actionReader frame (configuration sourceRuntime)) (S.actualOccurrence frame)
 have value := congrArg (fun source : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue W) (Var := X) (sort := s) => source.expression.eval source.environment) raw
 exact paid.trans (value.trans ((congrArg (fun env => Base.sourceCode.eval (pairEnvironment env (0 : Env W X)))
  (AI.actual_environment 0 frame)).trans (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Generic.pair_zero
   Base.fullNativeExpression frame.activeEnvironment)))

private theorem native_value (count : Nat) :
 (R.actionResultAt (actualFrame sourceRuntime count) (configuration sourceRuntime)
  (S.actualOccurrence (actualFrame sourceRuntime count))).2.2.1 =
 (((payloadAt (physicalRuntime sourceRuntime count).tick.next).sourceState,
   (payloadAt (physicalRuntime sourceRuntime count).tick.next).forcedTrace),0) := by
 have actual := congrArg (fun env => Base.fullNativeExpression.eval env) (environment_actual sourceRuntime count)
 have original := (SourcePhysicalContextRelationConsumer.nextTree (physicalRuntime sourceRuntime count)).sound
 exact (source_value sourceRuntime (actualFrame sourceRuntime count)).trans
  (congrArg (fun output : W s => (output,(0 : W s))) (actual.trans original))

theorem physicalReadback (count : Nat) : PhysicalReadback (physicalRuntime sourceRuntime count)
 (R.actionResultAt (actualFrame sourceRuntime count) (configuration sourceRuntime)
  (S.actualOccurrence (actualFrame sourceRuntime count))).2.2.1 := physical_readback (physicalRuntime sourceRuntime count)
 (R.actionResultAt (actualFrame sourceRuntime count) (configuration sourceRuntime)
  (S.actualOccurrence (actualFrame sourceRuntime count))).2.2.1 (native_value sourceRuntime count)

-- One source-generated method segment, with its exact selected settlement and next.
def actual_relation_cochain_method (start : Nat) :=
 let cfg := configuration sourceRuntime
 let receipt := S.Complete.receipt cfg (initial sourceRuntime) start
 let stop := start+receipt.1
 let selected := S.Complete.atReceipt cfg (initial sourceRuntime) start
 PProd.mk (installed_material sourceRuntime selected) <|
 PProd.mk (inheritedFaces sourceRuntime selected) <|
 PProd.mk (source_fields sourceRuntime selected) <|
 PProd.mk (paired_binding_square sourceRuntime stop) <|
 PProd.mk (word_forward sourceRuntime stop) <|
 PProd.mk (word_segment sourceRuntime start (receipt.1+1)) <|
 PProd.mk (physicalReadback sourceRuntime stop) <|
 PProd.mk (nativeForward sourceRuntime stop) <|
 PProd.mk (native_primitive_source sourceRuntime stop) <|
 PProd.mk (Context.WordExecution.forward_charge SourcePhysicalContextRelationConsumer.readPaired
  (point (physicalRuntime sourceRuntime stop)) (liftExpr fockOperation)) <|
 PProd.mk (original_paid_written sourceRuntime selected) <|
 PProd.mk (original_paid_consumed sourceRuntime selected) <|
 PProd.mk (born_stock_consumed sourceRuntime selected) <|
 PProd.mk (native_replay_written sourceRuntime stop) <|
 PProd.mk (native_replay_next_query sourceRuntime stop) <|
 PProd.mk (PM.Generic.birth_stock selected (sourceProgramme sourceRuntime)) <|
 PProd.mk (actualBoundary sourceRuntime stop) <|
 PProd.mk (generated_differential sourceRuntime stop) <|
 PProd.mk (completion_consumes_relation sourceRuntime stop) <|
 PProd.mk (sourceRelations sourceRuntime stop) <|
 PProd.mk (actual_boundary_from_source sourceRuntime stop) <|
 PProd.mk (actual_complex_boundary sourceRuntime stop) <|
 PProd.mk (actual_complex_differential sourceRuntime stop) <|
 PProd.mk (actualComplex sourceRuntime stop) <|
 PProd.mk (source_occurrence_erasure sourceRuntime stop) <|
 PProd.mk (source_occurrence_readback sourceRuntime stop) <|
 PProd.mk (actual_coimage_boundary sourceRuntime stop) <|
 PProd.mk (actual_coimage_differential sourceRuntime stop) <|
 PProd.mk (E.generated_action_embedding (faceAction sourceRuntime stop)
  ((E.generate (faceInput sourceRuntime (stop+1))).canonical (sourceRelationWord sourceRuntime stop))) <|
 PProd.mk (S.Complete.receipt_compiles cfg (initial sourceRuntime) start) <|
 PProd.mk (S.Complete.receipt_next cfg (initial sourceRuntime) start) <|
 PProd.mk (S.actual_query (initial sourceRuntime) cfg stop) <|
 PProd.mk ((inquiry sourceRuntime).tickAt stop).next_preservesGeneratedLivingLaw <|
 PProd.mk (S.actual_next (initial sourceRuntime) cfg stop)
 (SourceNativeInquiryRuntime.runFrom (runtime := inquiry sourceRuntime) (receipt.1+1)
  ((inquiry sourceRuntime).stateAt start))

end SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod.RelationCochain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
