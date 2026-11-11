import H0mework.Versions.Rdf421ff6.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.General
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.Recovery

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationNative SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
namespace AI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
 (withActualInput raw actual_environment actual_value)
end AI
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Seed cfg defaultFactory)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
 (Value groups)
end L
namespace PM
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
 (InstalledFaces completeQueryWritten)
namespace Generic
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Generic
 (pair_zero paid_expression birthStock birth_stock birth_keeps_callback)
end Generic
end PM
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation
 (Programme originalProgramme epoch optionalSourceRoot)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot root visit queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw
 compilationLaw datum actualOccurrence frames runtime next nextBorn targetAt target_root target_next
 actual_node actual_next actual_query)
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
 (receipt atReceipt receipt_compiles receipt_next)
end Complete
end S
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg stock_action_reader)
end AS
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (component stockLaw seed)
end I
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial registered)
end R
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
 (component combined configuration material face)
namespace E
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.Elimination
 (fourFaces dual_readback)
end E
end Faces

abbrev W := SourcePhysicalCalculation.CalculationValue
abbrev X := SourcePhysicalCalculation.CalculationVar
abbrev parentSort : Context.ContextSort OperationSort := Sum.inl OperationSort.parent
local instance zeroGroups : ∀ target, AddCommGroup (L.Value W 0 target) := L.groups W 0
abbrev PhysicalFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := W) (Var := X) (sort := parentSort)

-- Substitution acts on the complete native slot before the original observers materialize it.
def fullNativeExpression : Expr W X parentSort :=
 SourcePhysicalCalculation.rawExpression.subst Context.binding

def sourceCode : Expr (PairValue W) X parentSort := liftExpr fullNativeExpression

variable (sourceRuntime : LivingRuntimeState process)
abbrev initial := General.initial sourceRuntime

def initialSeed : SF.Seed W X parentSort 0 :=
 RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
  (initial sourceRuntime).registered.input.expression)

private def actualInputFactory :=
 AI.withActualInput sourceCode (SF.defaultFactory W X parentSort)

-- Only the code reader is taken from withActualInput; original lifecycle callbacks stay original.
def method : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := parentSort) :=
 { A.originalProgramme with datum := fun frame =>
    let original := A.originalProgramme.datum frame
    let calculated := (SF.cfg actualInputFactory 0 (initialSeed sourceRuntime)).datum frame
    { original with
      reader := calculated.calculationReader.getD original.reader
      calculationReader := calculated.calculationReader } }

private def paidQueryStock (frame : PhysicalFrame) :=
 SourceHistoryCommon.seed
  (SourceOperationPaidRelations.exposure (R.actualMaterial frame (method sourceRuntime)).state.2)
  (PM.completeQueryWritten 0 frame)

private def completePairOutput (frame : PhysicalFrame) :=
 Stock.preserve ((method sourceRuntime).nextPairInventory frame) (paidQueryStock sourceRuntime frame)

def sourceProgramme : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := parentSort) :=
 { Faces.configuration (method sourceRuntime) with
    nextPairInventory := fun frame => some (completePairOutput sourceRuntime frame) }

abbrev configuration := AS.stockCfg (sourceProgramme sourceRuntime)
def inquiry := S.runtime (initial sourceRuntime) (configuration sourceRuntime)
abbrev actualFrame (count : Nat) :=
 S.frames (initial sourceRuntime) (configuration sourceRuntime) count

private def installedFaces (frame : PhysicalFrame) :
 PM.InstalledFaces frame (method sourceRuntime) (configuration sourceRuntime) := by
 let base := sourceProgramme sourceRuntime
 let actual := configuration sourceRuntime
 let method := method sourceRuntime
 let installed := ((SourceNativeProjectionLaw.InstallationAt.componentCoface
  (A.optionalSourceRoot (S.base (A.epoch frame)).root (method.datum (A.epoch frame)).component).source.base
  (Faces.component (A.epoch frame) method)).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   { (S.base (A.epoch frame)).root.source.base with projectionLaw := Faces.combined (A.epoch frame) method }
   (I.stockLaw (A.epoch frame) base))) |>.trans
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


private theorem source_raw (frame : PhysicalFrame) :
 R.actionReader frame (configuration sourceRuntime) (S.actualOccurrence frame) =
 AI.raw 0 (A.epoch frame) sourceCode (S.actualOccurrence frame) := rfl

private theorem source_value (frame : PhysicalFrame) :
 (R.actionResultAt frame (configuration sourceRuntime) (S.actualOccurrence frame)).2.2.1 =
 (fullNativeExpression.eval frame.activeEnvironment, 0) := by
 have rawEq := source_raw sourceRuntime frame
 have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (S.baseRoot frame (configuration sourceRuntime)).toAuthoritativeRoot
  (R.actionReader frame (configuration sourceRuntime)) (S.actualOccurrence frame)
 have read := congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue W) (Var := X) (sort := parentSort) => raw.expression.eval raw.environment) rawEq
 exact paid.trans (read.trans ((congrArg (fun env => sourceCode.eval (pairEnvironment env (0 : Env W X)))
  (AI.actual_environment 0 frame)).trans (PM.Generic.pair_zero fullNativeExpression frame.activeEnvironment)))

-- The active environment is read from the installed paid material, never its old raw environment.
def activeWord (count : Nat) : Carrier process :=
 (N.input (SourceOperationInquiry.Context.Installation.materialAt
  (A.epoch (actualFrame sourceRuntime count))
  (S.actualOccurrence (actualFrame sourceRuntime count))).paid).environment
  (Sum.inr PUnit.unit) PUnit.unit

theorem active_word_current (count : Nat) : activeWord sourceRuntime count =
 (actualFrame sourceRuntime count).activeEnvironment (Sum.inr PUnit.unit) PUnit.unit :=
 congrArg (fun env => env (Sum.inr PUnit.unit) PUnit.unit)
  (AI.actual_environment 0 (actualFrame sourceRuntime count))

private theorem preserves_right {T : Type} (prior : Option (RootedAccountedUnfolding T))
 (tree : RootedAccountedUnfolding T) :
 ∀ event ∈ tree.trace, event ∈ (Stock.preserve prior tree).trace := by
 cases prior with
 | none => exact fun _ present => present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1

private theorem complete_callback (frame : PhysicalFrame) :
 ∀ event ∈ (PM.completeQueryWritten 0 frame).trace,
 event ∈ (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)).trace := by
 have born := PM.Generic.birth_keeps_callback frame (sourceProgramme sourceRuntime)
  (completePairOutput sourceRuntime frame) rfl
 intro event present
 exact born event (preserves_right _ _ event
  ((SourceHistoryCommon.parallel_right _ _ _).1 event present))

def source_target_consumer (count : Nat) :=
 let initial := initial sourceRuntime
 let cfg := configuration sourceRuntime
 let receipt := S.Complete.receipt cfg initial count
 let stop := count + receipt.1
 let selected := S.Complete.atReceipt cfg initial count
 PProd.mk (installedFaces sourceRuntime selected) <|
 PProd.mk (source_raw sourceRuntime selected) <|
 PProd.mk (source_value sourceRuntime selected) <|
 PProd.mk (active_word_current sourceRuntime stop) <|
 PProd.mk (PM.Generic.paid_expression selected cfg) <|
 PProd.mk (R.actualMaterial selected cfg) <|
 PProd.mk (complete_callback sourceRuntime selected) <|
 PProd.mk (PM.Generic.birth_stock selected (sourceProgramme sourceRuntime)) <|
 PProd.mk (S.Complete.receipt_compiles cfg initial count) <|
 PProd.mk (S.Complete.receipt_next cfg initial count) <|
 PProd.mk (S.actual_node initial cfg stop) <|
 PProd.mk (S.actual_query initial cfg stop) <|
 PProd.mk (S.actual_next initial cfg stop)
 ((inquiry sourceRuntime).tickAt stop).next_preservesGeneratedLivingLaw

open private Grounded frames_grounded advance_state from
 H0mework.Versions.Rdf421ff6.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.General

private theorem grounded_next_cfg (frame : PhysicalFrame) (clock : Nat)
 (source : Grounded frame clock) :
 Grounded (S.next frame (configuration sourceRuntime)) (clock+1) := by
 rcases source with ⟨coordinate, environment, nativeClock, currentClock⟩
 have noAt : (S.datum frame (configuration sourceRuntime)).nextEnvironmentReadAt = none := rfl
 have noRead : (S.datum frame (configuration sourceRuntime)).nextEnvironmentRead = none := rfl
 unfold S.next
 cases actual : frame.action with
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
  · intro current
    exact nativeClock current.1
  · change coordinate (frame.packetAt (RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathCurrent
     frame.old frame.registered frame.packetAt frame.depth).1).targetCurrent = clock+1
    exact (nativeClock _).trans (congrArg (fun value => value+1) currentClock)

private theorem frames_grounded_here (count : Nat) :
 Grounded (actualFrame sourceRuntime count) (sourceRuntime.state+11+count+1) := by
 induction count with
 | zero => exact frames_grounded sourceRuntime 0
 | succ count prior => exact grounded_next_cfg sourceRuntime (actualFrame sourceRuntime count) _ prior

theorem environment_actual (count : Nat) :
 (actualFrame sourceRuntime count).activeEnvironment =
 SourcePhysicalCalculation.rawEnvironment (sourceRuntime.advance (11+count)) := by
 obtain ⟨coordinate, environment, _nativeClock, currentClock⟩ := frames_grounded_here sourceRuntime count
 have actual := environment (RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathCurrent
  (actualFrame sourceRuntime count).old (actualFrame sourceRuntime count).registered
  (actualFrame sourceRuntime count).packetAt (actualFrame sourceRuntime count).depth).1
 change (actualFrame sourceRuntime count).activeEnvironment =
  Context.environment (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
   (statePoint process (coordinate _ - 1)) at actual
 rw [currentClock] at actual
 have state := advance_state sourceRuntime (11+count)
 change _ = Context.environment (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
  (statePoint process (sourceRuntime.advance (11+count)).state)
 rw [state]
 have clock : sourceRuntime.state+11+count+1-1 = sourceRuntime.state+(11+count) :=
  (Nat.add_sub_cancel (sourceRuntime.state+11+count) 1).trans (Nat.add_assoc _ _ _)
 exact actual.trans (congrArg (fun value =>
  Context.environment (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
   (statePoint process value)) clock)

theorem active_word_actual (count : Nat) : activeWord sourceRuntime count =
 point (sourceRuntime.advance (11+count)) :=
 (active_word_current sourceRuntime count).trans
  (congrArg (fun env => env (Sum.inr PUnit.unit) PUnit.unit) (environment_actual sourceRuntime count))

theorem next_active_word (count : Nat) :
 sourceAction process (activeWord sourceRuntime count) = activeWord sourceRuntime (count+1) := by
 rw [active_word_actual, active_word_actual]
 exact sourceAction_point (sourceRuntime.advance (11+count))

theorem actual_native_value (count : Nat) :
 (R.actionResultAt (actualFrame sourceRuntime count) (configuration sourceRuntime)
  (S.actualOccurrence (actualFrame sourceRuntime count))).2.2.1 =
 (((payloadAt (sourceRuntime.advance (11+count)).tick.next).sourceState,
   (payloadAt (sourceRuntime.advance (11+count)).tick.next).forcedTrace), 0) := by
 have generated := source_value sourceRuntime (actualFrame sourceRuntime count)
 have environment := congrArg (fun env => fullNativeExpression.eval env) (environment_actual sourceRuntime count)
 have source := (SourcePhysicalContextRelationConsumer.nextTree (sourceRuntime.advance (11+count))).sound
 exact generated.trans (congrArg (fun value => (value, (0 : W parentSort))) (environment.trans source))

end SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
