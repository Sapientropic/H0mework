import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Realization.Operations.CochainComplex
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.RelationProgramme
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
abbrev original := Context.Installation.rawAt frame occurrence
abbrev nextRaw := Context.Installation.nextRawAt frame occurrence
abbrev delta := (nextRaw frame occurrence).environment - (original frame occurrence).environment
abbrev word : Formal ℤ PhysicalValue (ChangedVar PhysicalVar) sort :=
  SourceOperationScalarCochain.updateWord (R:=ℤ) (original frame occurrence).expression

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue)
    (Var:=ChangedVar PhysicalVar) (sort:=sort) :=
  ⟨pairEnvironment (mixedEnvironment (original frame occurrence).environment (delta frame occurrence)) 0,
    liftExpr (SourceOperationExecution.Coefficients.expression (word frame occurrence))⟩

abbrev Ledger := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.ledgerRoot frame.registered frame.packetAt

def material := (Context.Installation.materialAt frame occurrence,
  word frame occurrence,RootedAccountedUnfolding.zero
    (CofinalHistorySettlement.PresentedRelationEventAt.relation (word frame occurrence)),raw frame occurrence,
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
    (Mother.baseState { frame with depth := 0 }).root.toAuthoritativeRoot occurrence)

def component : SourceNativeProjectionLaw
    (Mother.baseState { frame with depth := 0 }).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} supplied _ => type_of% (material frame supplied)
  project := fun _ {_current} supplied _ => material frame supplied

def installedReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  ((component frame).project PUnit.unit supplied PUnit.unit).2.2.2.1

def programme : Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) where
  LowVar := ChangedVar PhysicalVar
  datum sourceFrame := { component := some (component sourceFrame),reader := installedReader sourceFrame }
end SourceOperationInquiry.Context.Faces.Execution.Activation.RelationProgramme
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
