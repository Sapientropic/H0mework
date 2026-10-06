import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch.Consumer
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Finite.Batch
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch.Calls
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count iterations : Nat)
namespace F
export SourceOperationInquiry.Context.Native.Orbit.Finite.Batch (bound original_query)
end F
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query resultAt actualOccurrence baseRoot datum)
end Shared
abbrev sourceSeed := Batch.sourceSeed frame configuration sourceStage stage count
abbrev bound := F.bound (sourceSeed frame configuration sourceStage stage count) iterations
abbrev CallIndex := Fin (bound frame configuration sourceStage stage count iterations+2)
def callMaterial (index : CallIndex frame configuration sourceStage stage count iterations) :=
 let current := Future.frameAt frame configuration sourceStage stage (count+index.val)
 let consumer := Future.consumer frame configuration sourceStage stage
 let occurrence := Shared.actualOccurrence current
 (current.rawRead,Shared.query current consumer,Shared.resultAt current consumer occurrence,
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
  current.currentState.root.toAuthoritativeRoot occurrence)
def observations := fun index : CallIndex frame configuration sourceStage stage count iterations =>
 (callMaterial frame configuration sourceStage stage count iterations index).1.environment
private def snapshotOld {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)]
 (bound : Nat) (observations : Fin (bound+2) → Env A X) : Env A (SourceOperationInquiry.Context.Native.Orbit.Var X) :=
 fun target name => if bounded : name.1≤bound then observations ⟨name.1,by omega⟩ target name.2 else 0
private def snapshotIncrement {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)]
 (bound : Nat) (observations : Fin (bound+2) → Env A X) : Env A (SourceOperationInquiry.Context.Native.Orbit.Var X) :=
 fun target name => if bounded : name.1≤bound then observations ⟨name.1+1,by omega⟩ target name.2-
  observations ⟨name.1,by omega⟩ target name.2 else 0
theorem snapshots_source {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)] {t : T}
 {p : SourceNativeInquiryEngineProcess.{u}} (r : SourceNativeInquiryRuntime p)
 (input : SourceOperationInquiry.Context.RawSource (PhysicalValue:=A) (PhysicalVar:=X) (sort:=t) r)
 (offset bound : Nat) (data : Fin (bound+2) → Env A X)
 (generated : ∀ index,data index=SourceOperationInquiry.Context.readEnv r input (r.stateAt (offset+index.val))) :
 snapshotOld bound data=SourceOperationInquiry.Context.Native.Orbit.Finite.finiteOld r input offset bound ∧
 snapshotIncrement bound data=SourceOperationInquiry.Context.Native.Orbit.Finite.finiteIncrement r input offset bound := by
 constructor
 · funext target name
   unfold snapshotOld SourceOperationInquiry.Context.Native.Orbit.Finite.finiteOld
   split
   · rw [generated]
     simp only [SourceOperationInquiry.Context.Native.Orbit.Finite.environments,List.get_ofFn,Fin.val_cast]
   · rfl
 · funext target name
   unfold snapshotIncrement SourceOperationInquiry.Context.Native.Orbit.Finite.finiteIncrement
   split
   · rw [generated,generated]
     simp only [SourceOperationInquiry.Context.Native.Orbit.Finite.environments,List.get_ofFn,Fin.val_cast]
   · rfl
abbrev old := snapshotOld (bound frame configuration sourceStage stage count iterations)
 (observations frame configuration sourceStage stage count iterations)
abbrev increment := snapshotIncrement (bound frame configuration sourceStage stage count iterations)
 (observations frame configuration sourceStage stage count iterations)
abbrev expression := Batch.expression frame configuration sourceStage stage count iterations
def environment := InventoryVector.environment (SourceOperationInquiry.Context.Native.Pairing.Orbit.Batch.Index iterations)
 (pairEnvironment (old frame configuration sourceStage stage count iterations) (increment frame configuration sourceStage stage count iterations))
def raw := (⟨environment frame configuration sourceStage stage count iterations,
 expression frame configuration sourceStage stage count iterations⟩ : RootGeneratedDebtActivationJointSource.OwnerFree.Raw)
def material := (Batch.material frame configuration sourceStage stage count iterations,
 callMaterial frame configuration sourceStage stage count iterations,raw frame configuration sourceStage stage count iterations)
def component : SourceNativeProjectionLaw (Batch.root frame configuration sourceStage stage count iterations).source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration sourceStage stage count iterations)
 project := fun _ {_current} _ _ => material frame configuration sourceStage stage count iterations
def baseRoot := (Batch.root frame configuration sourceStage stage count iterations).withProjectionCoface (component frame configuration sourceStage stage count iterations)
def reader {current : type_of% (Query.original frame configuration sourceStage stage count).visit.current}
 (_supplied : (Query.original frame configuration sourceStage stage count).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration sourceStage stage count iterations).project PUnit.unit (Query.occurrence frame configuration sourceStage stage count) PUnit.unit).2.2
def sourceInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Batch.root frame configuration sourceStage stage count iterations).source.base (component frame configuration sourceStage stage count iterations)
def sourceFace : SourceNativeRootSemanticFaceAt (baseRoot frame configuration sourceStage stage count iterations)
 (Query.original frame configuration sourceStage stage count).visit where
 projection := (sourceInstallation frame configuration sourceStage stage count iterations).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot (reader frame configuration sourceStage stage count iterations)
 (Query.occurrence frame configuration sourceStage stage count)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot (reader frame configuration sourceStage stage count iterations)
def root := (baseRoot frame configuration sourceStage stage count iterations).withProjectionCoface (queryLaw frame configuration sourceStage stage count iterations)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (baseRoot frame configuration sourceStage stage count iterations).source.base (queryLaw frame configuration sourceStage stage count iterations)
def face : SourceNativeRootSemanticFaceAt (root frame configuration sourceStage stage count iterations)
 (Query.original frame configuration sourceStage stage count).visit where
 projection := (installed frame configuration sourceStage stage count iterations).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (root frame configuration sourceStage stage count iterations) (Query.original frame configuration sourceStage stage count).visit
 (Query.original frame configuration sourceStage stage count).U7 (Query.original frame configuration sourceStage stage count).calculus
 (reader frame configuration sourceStage stage count iterations)
abbrev generated := (Batch.paidGenerated frame configuration sourceStage stage count iterations,sourceFace frame configuration sourceStage stage count iterations,
 face frame configuration sourceStage stage count iterations,SourceGeneratedInquiryReceiptAction.actualGenerated
 (queryFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch.Calls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
