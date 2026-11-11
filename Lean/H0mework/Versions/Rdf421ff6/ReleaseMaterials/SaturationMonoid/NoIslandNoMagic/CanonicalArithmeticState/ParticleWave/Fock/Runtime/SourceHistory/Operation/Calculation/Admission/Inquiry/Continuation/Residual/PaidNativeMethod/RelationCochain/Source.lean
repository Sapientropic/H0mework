import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Context.WordExecution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.PaidNativeMethod.Consumer
import H0mework.Versions.R2.Realization.Operations.Context.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Words
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
import H0mework.Realization.Operations.Substitution.Complex
import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceEvaluationKernel

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod.RelationCochain
open CategoryTheory RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationNative
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
attribute [local instance] SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod.zeroGroups
namespace Base
export SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod
 (W X parentSort PhysicalFrame initial method sourceProgramme sourceCode fullNativeExpression)
end Base
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch optionalSourceRoot)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot root visit queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw
 datum actualOccurrence frames runtime next nextBorn actual_node actual_query actual_next)
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
 (receipt atReceipt receipt_compiles receipt_next)
end Complete
end S
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg)
end AS
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace C
export SourceOperationInquiry.Context.Installation (residualAt materialAt Occurrence)
end C
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (component stockLaw seed)
end I
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader actionResultAt)
end R
namespace PM
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod (completeQueryWritten)
namespace Generic
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Generic (birthStock birth_stock birth_keeps_callback)
end Generic
end PM
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
namespace Joint
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (complete_written_preserves history)
end Joint
namespace Res
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (pairInventory priorPairInventory)
end Res

abbrev W := Base.W
abbrev X := Base.X
abbrev s := Base.parentSort
abbrev Frame := Base.PhysicalFrame
abbrev pairBinding : ∀ target, X target → Expr (PairValue W) X target :=
 fun target name => liftExpr (Context.binding target name)
abbrev originalExpression : Expr (PairValue W) X s := liftExpr SourcePhysicalCalculation.rawExpression

def paidEnvironment (frame : Frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (o : C.Occurrence (A.epoch frame) (current := current)) : Env W X :=
 (N.input (C.residualAt (A.epoch frame) o)).environment

def pairEnvironmentAt (frame : Frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (o : C.Occurrence (A.epoch frame) (current := current)) : Env (PairValue W) X :=
 pairEnvironment (paidEnvironment frame o) 0

def sourceWord (frame : Frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (o : C.Occurrence (A.epoch frame) (current := current)) : Carrier process :=
 paidEnvironment frame o (Sum.inr PUnit.unit) PUnit.unit

theorem context_environment (frame : Frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (o : C.Occurrence (A.epoch frame) (current := current)) :
 Context.environment (PhysicalValue := PairValue OperationValue) (sourceWord frame o) = paidEnvironment frame o := by
 funext sort name
 cases sort with
 | inl _ => exact PEmpty.elim name
 | inr tag => cases tag; cases name; rfl

private def transportPairEnv {first second : Env (PairValue W) X}
 {before after : Expr (PairValue W) X s} (same : first = second)
 (paid : Trace first before after) : Trace second before after :=
 Eq.mp (congrArg (fun env => Trace env before after) same) paid

-- The callback retains this original native schedule, not a new canonical execution.
def sourceTrace (frame : Frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (o : C.Occurrence (A.epoch frame) (current := current)) :=
 Context.WordExecution.embeddedTrace SourcePhysicalContextRelationConsumer.readPaired
  (sourceAction process (sourceWord frame o))
  (execution (Context.WordExecution.observerEnvironment SourcePhysicalContextRelationConsumer.readPaired
   (sourceAction process (sourceWord frame o))) (liftExpr fockOperation))

def replay (frame : Frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (o : C.Occurrence (A.epoch frame) (current := current)) :=
 transportPairEnv (congrArg (fun env => pairEnvironment env (0 : Env W X)) (context_environment frame o))
  (Context.WordExecution.pairedForward SourcePhysicalContextRelationConsumer.readPaired (sourceWord frame o)
   (liftExpr fockOperation))

def replayStock (frame : Frame) :=
 SourceOperationPaidRelations.exposure (replay frame (S.actualOccurrence frame))

def material (frame : Frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (o : C.Occurrence (A.epoch frame) (current := current)) :=
 (C.materialAt (A.epoch frame) o, replay frame o,
  SourceOperationPaidRelations.exposure (replay frame o),
  SourceSubstitution.complexMorphism (R := ℤ) (s := s) pairBinding (pairEnvironmentAt frame o))

variable (sourceRuntime : LivingRuntimeState process)

def replayComponent (frame : Frame) : SourceNativeProjectionLaw
 (S.base (A.epoch frame)).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit
 ActiveAt := fun _ {_current} _ => PUnit
 InactiveAt := fun _ {_current} _ => PEmpty
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} o _ => type_of% (material frame o)
 project := fun _ {_current} o _ => material frame o

def combined (frame : Frame) :=
 ((A.optionalSourceRoot (S.base (A.epoch frame)).root
   ((Base.sourceProgramme sourceRuntime).datum (A.epoch frame)).component).source.base.withProjectionCoface
  (replayComponent frame)).projectionLaw

def callback (frame : Frame) :=
 Stock.preserve ((Base.sourceProgramme sourceRuntime).nextPairInventory frame) (replayStock frame)

-- The fixed original native reader and both none decoders remain source-owned.
def sourceProgramme : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s) :=
 { Base.sourceProgramme sourceRuntime with
   datum := fun frame => { (Base.sourceProgramme sourceRuntime).datum frame with
    component := some (combined sourceRuntime frame) }
   nextPairInventory := fun frame => some (callback sourceRuntime frame) }

abbrev configuration := AS.stockCfg (sourceProgramme sourceRuntime)
abbrev initial := Base.initial sourceRuntime
def inquiry := S.runtime (initial sourceRuntime) (configuration sourceRuntime)
abbrev actualFrame (count : Nat) := S.frames (initial sourceRuntime) (configuration sourceRuntime) count

abbrev Reader (frame : Frame) :=
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} →
 C.Occurrence frame (current := current) →
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := PairValue W) (Var := X) (sort := s)

theorem source_fields (frame : Frame) :
 @Eq (Reader frame) ((sourceProgramme sourceRuntime).datum frame).reader
  ((Base.sourceProgramme sourceRuntime).datum frame).reader ∧
 @Eq (Option (Reader frame)) ((sourceProgramme sourceRuntime).datum frame).calculationReader
  ((Base.sourceProgramme sourceRuntime).datum frame).calculationReader ∧
 ((sourceProgramme sourceRuntime).datum frame).nextEnvironmentReadAt = none ∧
 ((sourceProgramme sourceRuntime).datum frame).nextEnvironmentRead = none := ⟨rfl,rfl,rfl,rfl⟩

private def installed (frame : Frame) :=
 ((SourceNativeProjectionLaw.InstallationAt.componentCoface
  (A.optionalSourceRoot (S.base (A.epoch frame)).root
   ((Base.sourceProgramme sourceRuntime).datum (A.epoch frame)).component).source.base
  (replayComponent frame)).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   { (S.base (A.epoch frame)).root.source.base with projectionLaw := combined sourceRuntime frame }
   (I.stockLaw (A.epoch frame) (sourceProgramme sourceRuntime)))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
  (I.component (A.epoch frame) (sourceProgramme sourceRuntime))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame (configuration sourceRuntime)).source.base
  (S.queryLaw (A.epoch frame) (configuration sourceRuntime))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame (configuration sourceRuntime)).source.base
  (S.resultLaw (A.epoch frame) (configuration sourceRuntime))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame (configuration sourceRuntime)).source.base
  (S.consumerLaw (A.epoch frame) (configuration sourceRuntime))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame (configuration sourceRuntime)).source.base
  (S.compilationLaw (A.epoch frame) (configuration sourceRuntime)))

def face (frame : Frame) : SourceNativeRootSemanticFaceAt
 (S.root frame (configuration sourceRuntime)) (S.visit frame (configuration sourceRuntime)) where
 projection := (installed sourceRuntime frame).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

theorem installed_material (frame : Frame) : (face sourceRuntime frame).rootRead =
 material frame (S.actualOccurrence frame) := rfl

private theorem preserve_right {T : Type} (prior : Option (RootedAccountedUnfolding T))
 (tree : RootedAccountedUnfolding T) :
 ∀ event ∈ tree.trace, event ∈ (Stock.preserve prior tree).trace := by
 cases prior with
 | none => exact fun _ present => present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1

theorem replay_written (frame : Frame) :
 ∀ event ∈ (replayStock frame).trace,
 event ∈ (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)).trace := by
 have carry := PM.Generic.birth_keeps_callback frame (sourceProgramme sourceRuntime)
  (callback sourceRuntime frame) rfl
 exact fun event present => carry event (preserve_right _ _ event present)

theorem replay_next_query (frame : Frame) :
 ∀ event ∈ (replayStock frame).trace,
 event ∈ (PM.completeQueryWritten 0 (S.nextBorn frame (configuration sourceRuntime))).trace := by
 let born := S.nextBorn frame (configuration sourceRuntime)
 have inventory : (A.epoch born).pairInventory =
  some (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)) :=
  PM.Generic.birth_stock frame (sourceProgramme sourceRuntime)
 intro event present
 apply Joint.complete_written_preserves (I.seed born) (A.epoch born) (S.actualOccurrence born) event
 unfold Res.pairInventory Res.priorPairInventory
 rw [inventory]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_left _ _ _).1 event (replay_written sourceRuntime frame event present))

open private Grounded frames_grounded advance_state from
 H0mework.Versions.Rdf421ff6.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.General

private theorem grounded_next (frame : Frame) (clock : Nat) (source : Grounded frame clock) :
 Grounded (S.next frame (configuration sourceRuntime)) (clock+1) := by
 rcases source with ⟨coordinate, environment, nativeClock, currentClock⟩
 have noAt : (S.datum frame (configuration sourceRuntime)).nextEnvironmentReadAt = none := rfl
 have noRead : (S.datum frame (configuration sourceRuntime)).nextEnvironmentRead = none := rfl
 unfold S.next
 cases frame.action with
 | inr paid =>
  refine ⟨coordinate, environment, nativeClock, ?_⟩
  change coordinate (frame.packetAt (RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathCurrent
   frame.old frame.registered frame.packetAt frame.depth).1).targetCurrent = clock+1
  exact (nativeClock _).trans (congrArg (fun value => value+1) currentClock)
 | inl settled =>
  refine ⟨fun current => coordinate current.1, ?_, ?_, ?_⟩
  · intro current
    simp only [S.nextBorn, noAt, noRead]
    exact environment current.1
  · exact fun current => nativeClock current.1
  · change coordinate (frame.packetAt (RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathCurrent
     frame.old frame.registered frame.packetAt frame.depth).1).targetCurrent = clock+1
    exact (nativeClock _).trans (congrArg (fun value => value+1) currentClock)

private theorem actual_grounded (count : Nat) :
 Grounded (actualFrame sourceRuntime count) (sourceRuntime.state+11+count+1) := by
 induction count with
 | zero => exact frames_grounded sourceRuntime 0
 | succ count prior => exact grounded_next sourceRuntime _ _ prior

theorem environment_actual (count : Nat) : (actualFrame sourceRuntime count).activeEnvironment =
 SourcePhysicalCalculation.rawEnvironment (sourceRuntime.advance (11+count)) := by
 obtain ⟨coordinate, environment, _nativeClock, currentClock⟩ := actual_grounded sourceRuntime count
 have actual := environment (RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathCurrent
  (actualFrame sourceRuntime count).old (actualFrame sourceRuntime count).registered
  (actualFrame sourceRuntime count).packetAt (actualFrame sourceRuntime count).depth).1
 change (actualFrame sourceRuntime count).activeEnvironment = Context.environment
  (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
  (statePoint process (coordinate _-1)) at actual
 rw [currentClock] at actual
 have state := advance_state sourceRuntime (11+count)
 change _ = Context.environment (PhysicalValue := PairValue OperationValue)
  (statePoint process (sourceRuntime.advance (11+count)).state)
 rw [state]
 have clock : sourceRuntime.state+11+count+1-1 = sourceRuntime.state+(11+count) :=
  (Nat.add_sub_cancel (sourceRuntime.state+11+count) 1).trans (Nat.add_assoc _ _ _)
 exact actual.trans (congrArg (fun value => Context.environment (PhysicalValue := PairValue OperationValue)
  (statePoint process value)) clock)

theorem paid_current (count : Nat) :
 paidEnvironment (actualFrame sourceRuntime count) (S.actualOccurrence (actualFrame sourceRuntime count)) =
 (actualFrame sourceRuntime count).activeEnvironment :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.actual_environment 0 _

abbrev actualPairEnv (count : Nat) := pairEnvironmentAt (actualFrame sourceRuntime count)
 (S.actualOccurrence (actualFrame sourceRuntime count))

theorem paired_binding_square (count : Nat) :
 SourceSubstitution.sourceEnvironment pairBinding (actualPairEnv sourceRuntime count) =
 actualPairEnv sourceRuntime (count+1) := by
 funext target name
 change (liftExpr (Context.binding target name)).eval (actualPairEnv sourceRuntime count) = _
 dsimp only [actualPairEnv, pairEnvironmentAt]
 rw [SourceOperationScalarInventoryLift.eval_liftExpr]
 simp only [paid_current, environment_actual]
 rw [SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Generic.effect_zero]
 exact congrArg (fun env => (env target name, (0 : W target)))
  (Context.binding_eval (PhysicalValue := PairValue OperationValue) (sourceRuntime.advance (11+count)))

end SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod.RelationCochain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
