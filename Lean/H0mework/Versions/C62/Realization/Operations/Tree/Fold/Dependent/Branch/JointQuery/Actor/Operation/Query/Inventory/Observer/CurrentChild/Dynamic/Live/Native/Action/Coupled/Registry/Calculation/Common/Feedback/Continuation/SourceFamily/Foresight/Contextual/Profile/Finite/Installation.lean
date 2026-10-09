import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Indexed

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed
namespace Installation
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base root baseRoot queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw visit)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme optionalSourceRoot epoch)
end E
namespace Original
export Lower.SourceFamily.Foresight.Contextual.Installed (configuration)
end Original
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))

private def sourceLaw {N:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
 (source:SourceNativeLedgerSource N V)
 (family:{current:V.Current}→source.source.toRootSource.actual.OccurrenceAt current→Type u)
 (producer:{current:V.Current}→(occurrence:source.source.toRootSource.actual.OccurrenceAt current)→family occurrence):
 SourceNativeProjectionLaw source where
 Projection:=PUnit.{u+1}
 ActiveAt:=fun _ {_current} _=>PUnit.{u+1}
 InactiveAt:=fun _ {_current} _=>PEmpty.{u+1}
 classify:=fun _ {_current} _=>.inl PUnit.unit
 PayloadAt:=fun _ {_current} supplied _=>family supplied
 project:=fun _ {_current} supplied _=>producer supplied

def component:SourceNativeProjectionLaw
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.ledgerRoot frame.registered frame.packetAt).source:=
 sourceLaw
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.ledgerRoot frame.registered frame.packetAt).source
  (fun {current} supplied=>OutputAt binding n seed frame ⟨current,supplied⟩
   (disposition binding n seed frame ⟨current,supplied⟩))
  (fun {current} supplied=>output binding n seed frame ⟨current,supplied⟩)

abbrev originalRoot:=E.optionalSourceRoot (Q.base frame).root
 ((Original.configuration binding n seed).datum frame).component
def combined:=(originalRoot binding n seed frame).source.base.withProjectionCoface
 (component binding n seed frame) |>.projectionLaw

def configuration:E.Programme (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s) where
 LowVar:=X
 datum sourceFrame:={
   component:=some (combined binding n seed sourceFrame)
   reader:=((Original.configuration binding n seed).datum sourceFrame).reader
   calculationReader:=none
   nextEnvironmentRead:=((Original.configuration binding n seed).datum sourceFrame).nextEnvironmentRead
   nextEnvironmentReadAt:=((Original.configuration binding n seed).datum sourceFrame).nextEnvironmentReadAt}
 nextInventory:=(Original.configuration binding n seed).nextInventory
 nextPairInventory:=(Original.configuration binding n seed).nextPairInventory

theorem original_reader {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)):
 ((configuration binding n seed).datum frame).reader supplied=
 ((Original.configuration binding n seed).datum frame).reader supplied:=rfl

theorem original_inventory:(configuration binding n seed).nextInventory=
 (Original.configuration binding n seed).nextInventory:=rfl

theorem original_pair_inventory:(configuration binding n seed).nextPairInventory=
 (Original.configuration binding n seed).nextPairInventory:=rfl

theorem original_decoder:
 ((configuration binding n seed).datum frame).nextEnvironmentRead=
 ((Original.configuration binding n seed).datum frame).nextEnvironmentRead ∧
 ((configuration binding n seed).datum frame).nextEnvironmentReadAt=
 ((Original.configuration binding n seed).datum frame).nextEnvironmentReadAt:=⟨rfl,rfl⟩

def installation:=
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (originalRoot binding n seed (E.epoch frame)).source.base
  (component binding n seed (E.epoch frame))).trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (Q.base frame).root.source.base
  (combined binding n seed (E.epoch frame))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.baseRoot frame (configuration binding n seed)).source.base
  (Q.queryLaw (E.epoch frame) (configuration binding n seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.queryRoot frame (configuration binding n seed)).source.base
  (Q.resultLaw (E.epoch frame) (configuration binding n seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.resultRoot frame (configuration binding n seed)).source.base
  (Q.consumerLaw (E.epoch frame) (configuration binding n seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.consumerRoot frame (configuration binding n seed)).source.base
  (Q.compilationLaw (E.epoch frame) (configuration binding n seed)))

end Installation
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
