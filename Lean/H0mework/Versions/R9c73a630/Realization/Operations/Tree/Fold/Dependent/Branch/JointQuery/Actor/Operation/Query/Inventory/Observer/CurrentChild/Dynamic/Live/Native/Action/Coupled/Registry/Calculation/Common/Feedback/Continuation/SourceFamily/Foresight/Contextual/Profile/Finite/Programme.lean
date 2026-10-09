import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Consumer
import H0mework.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Charge
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource
namespace InstalledQuery
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot queryRoot resultRoot consumerRoot root queryLaw resultLaw consumerLaw compilationLaw actualOccurrence actualVisit resultAt query visit resultFace)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme optionalSourceRoot)
end E
namespace Receipt
export SourceGeneratedInquiryReceiptAction
 (actualMaterial registered generatedAction literal_next whole_first successor_valid source_effect source_inverse)
end Receipt
variable {S : Type u} {V X : S→Type u} [∀t,AddCommGroup (V t)] {s:S}
variable (sigma:∀t,X t→Expr V X t) (word:Formal ℤ (PairValue V) X s)
variable (original:E.Programme (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s))
variable (frame:M.Frame (Value:=V) (Var:=X) (sort:=s))
def environment {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)):=
 Core.pair sigma (SourceOperationInquiry.Context.Native.Orbit.Installation.cursorAt frame supplied)
def reader {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)):=
 queryRaw (environment sigma frame supplied) word

def materialAt {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)):=
 (frame.inventory,frame.pairInventory,
  Owned.I.resultAt (Q.base frame).root.toAuthoritativeRoot (reader sigma word frame) supplied,
  fun count:Fin (Coefficients.cost word+1)=>Owned.I.sourceMaterialAt
    (Owned.authoritativeRoot (Q.base frame).root.toAuthoritativeRoot current (fun _=>reader sigma word frame supplied))
    ((Owned.authoritativeRoot (Q.base frame).root.toAuthoritativeRoot current (fun _=>reader sigma word frame supplied)).emitted
      (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
       (Q.base frame).root.toAuthoritativeRoot current (fun _=>reader sigma word frame supplied) count.1)))
def component:SourceNativeProjectionLaw (Q.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit.{u+1}
 ActiveAt:=fun _ {_current} _=>PUnit.{u+1}
 InactiveAt:=fun _ {_current} _=>PEmpty.{u+1}
 classify:=fun _ {_current} _=>.inl PUnit.unit
 PayloadAt:=fun _ {_current} supplied _=>type_of% (materialAt sigma word frame supplied)
 project:=fun _ {_current} supplied _=>materialAt sigma word frame supplied
abbrev oldRoot:=E.optionalSourceRoot (Q.base frame).root (original.datum frame).component
def combined:=(oldRoot original frame).source.base.withProjectionCoface (component sigma word frame) |>.projectionLaw
def written:=SourceOperationPaidRelations.exposure
 (Owned.I.resultAt (Q.base frame).root.toAuthoritativeRoot (reader sigma word frame) (Q.actualOccurrence frame)).2.1.2

def programme:E.Programme (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s) where
 LowVar:=X
 datum sourceFrame:={
  component:=some (combined sigma word original sourceFrame)
  reader:=fun {_current} supplied=>((component sigma word sourceFrame).project PUnit.unit supplied PUnit.unit).2.2.1.1
  calculationReader:=none
  nextEnvironmentRead:=(original.datum sourceFrame).nextEnvironmentRead
  nextEnvironmentReadAt:=(original.datum sourceFrame).nextEnvironmentReadAt}
 nextInventory:=original.nextInventory
 nextPairInventory:=fun sourceFrame=>some (T.preserve (original.nextPairInventory sourceFrame)
  (written sigma word sourceFrame))

def installation:=
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (oldRoot original (E.epoch frame)).source.base
  (component sigma word (E.epoch frame))).trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (Q.base frame).root.source.base
  (combined sigma word original (E.epoch frame))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.baseRoot frame (programme sigma word original)).source.base
  (Q.queryLaw (E.epoch frame) (programme sigma word original))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.queryRoot frame (programme sigma word original)).source.base
  (Q.resultLaw (E.epoch frame) (programme sigma word original))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.resultRoot frame (programme sigma word original)).source.base
  (Q.consumerLaw (E.epoch frame) (programme sigma word original))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.consumerRoot frame (programme sigma word original)).source.base
  (Q.compilationLaw (E.epoch frame) (programme sigma word original)))
def face:SourceNativeRootSemanticFaceAt (Q.root frame (programme sigma word original)) (Q.visit frame (programme sigma word original)) where
 projection:=(installation sigma word original frame).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl

theorem actual_source:(face sigma word original frame).rootRead=
 materialAt sigma word (E.epoch frame) (Q.actualOccurrence frame):=rfl

theorem actual_raw:(Q.query frame (programme sigma word original)).raw=
 queryRaw (environment sigma (E.epoch frame) (Q.actualOccurrence frame)) word:=rfl

theorem actual_value:(Q.resultFace frame (programme sigma word original)).rootRead.2.2.1=
 evaluation (R:=ℤ) (environment sigma (E.epoch frame) (Q.actualOccurrence frame)) word:=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans (Coefficients.expression_eval word _)

theorem actual_exposure:SourceOperationPaidRelations.exposure (Q.resultFace frame (programme sigma word original)).rootRead.2.1.2=
 written sigma word frame:=
 RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
  (Q.baseRoot frame (programme sigma word original)).toAuthoritativeRoot (Q.visit frame (programme sigma word original)).current
  (Q.base frame).root.toAuthoritativeRoot (Q.actualVisit frame).current (reader sigma word (E.epoch frame) (Q.actualOccurrence frame))

theorem actual_paid_into_next (event:PresentedRelationEventAt (Expr (PairValue V) X s)) :
 event ∈ (written sigma word frame).trace →
 event ∈ (((programme sigma word original).nextPairInventory frame).getD (written sigma word frame)).trace:=by
 intro present
 change event∈(T.preserve (original.nextPairInventory frame) (written sigma word frame)).trace
 unfold T.preserve
 cases original.nextPairInventory frame with
 | none=>exact present
 | some prior=>exact (SourceHistoryCommon.parallel_right _ _ _).1 _ present

theorem actual_owner:(Receipt.actualMaterial frame (programme sigma word original)).owner=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.entryAt frame (Q.actualOccurrence frame):=rfl

theorem actual_request:(Receipt.actualMaterial frame (programme sigma word original)).raw=(queryRaw
 (environment sigma (E.epoch frame) (Q.actualOccurrence frame)) word).expression:=rfl

theorem actual_update:type_of% (SourceGeneratedInquiryReceiptAction.actual_updated_environment frame (programme sigma word original)):=
 SourceGeneratedInquiryReceiptAction.actual_updated_environment _ _

theorem actual_whole:type_of% (Receipt.whole_first frame (programme sigma word original)):=Receipt.whole_first _ _
theorem actual_next:type_of% (Receipt.literal_next frame (programme sigma word original)):=Receipt.literal_next _ _
theorem actual_valid:type_of% (Receipt.successor_valid frame (programme sigma word original)):=Receipt.successor_valid _ _
end InstalledQuery
namespace InstalledQuery
variable {S:Type u} {V X:S→Type u} [∀t,AddCommGroup (V t)] {s:S}
variable (sigma:∀t,X t→Expr V X t) (word:Formal ℤ (PairValue V) X s)
variable (original:E.Programme (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s))
variable (frame:M.Frame (Value:=V) (Var:=X) (sort:=s))
theorem environment_source {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)):
 environment sigma frame supplied=Future.Replay.Source.pairEnvironment sigma frame supplied:=by
 rcases supplied with ⟨support,event⟩
 cases event
 rfl

def compiled:=((Q.resultFace frame (programme sigma word original)).rootRead,
 (face sigma word original frame).rootRead,Receipt.generatedAction frame (programme sigma word original))

theorem charge (seen:evaluation (R:=ℤ) (environment sigma (E.epoch frame) (Q.actualOccurrence frame)) word≠0):
 2≤remaining (Q.query frame (programme sigma word original)).raw.expression :=
 Coefficients.SourceCharge.expression_charge word
  (fun zero=>seen ((congrArg (evaluation (R:=ℤ) (environment sigma (E.epoch frame) (Q.actualOccurrence frame))) zero).trans (map_zero _)))

theorem exact_fee:(Q.resultFace frame (programme sigma word original)).rootRead.2.1.2.length=Coefficients.cost word:=
 (Owned.I.source_history _ _ _).trans (Coefficients.expression_remaining word)

theorem old_scalar:(programme sigma word original).nextInventory=original.nextInventory:=rfl

theorem decoder_exact:((programme sigma word original).datum frame).nextEnvironmentRead=
 (original.datum frame).nextEnvironmentRead ∧
 ((programme sigma word original).datum frame).nextEnvironmentReadAt=(original.datum frame).nextEnvironmentReadAt:=⟨rfl,rfl⟩

theorem old_pair (prior) (present:original.nextPairInventory frame=some prior) (event)
 (member:event∈prior.trace):event∈(((programme sigma word original).nextPairInventory frame).getD (written sigma word frame)).trace:=by
 change event∈(T.preserve (original.nextPairInventory frame) (written sigma word frame)).trace
 unfold T.preserve
 rw [present]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ member
end InstalledQuery
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
