import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Renewal.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
abbrev originalRaw := installedReader seed frame occurrence
abbrev sourceResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (Shared.baseRoot frame (programme seed)).toAuthoritativeRoot (installedReader seed frame) occurrence
abbrev original := (Shared.baseRoot frame (programme seed)).toAuthoritativeRoot
abbrev originalReader := fun (_supplied : (original seed frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) =>
  originalRaw seed frame occurrence
abbrev calculationRoot := RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot
  (original seed frame) current (originalReader seed frame occurrence)
abbrev endpoint := (sourceResult seed frame occurrence).2.1
abbrev ReceiptOccurrence := (calculationRoot seed frame occurrence).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  (endpoint seed frame occurrence)
def requestMaterial (supplied : ReceiptOccurrence seed frame occurrence) :
    RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
      (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) supplied := by
  rcases supplied with ⟨support,event⟩
  cases event
  exact { environment := (originalRaw seed frame occurrence).environment
          increment := Action.updatedPairEnvironment frame occurrence - (originalRaw seed frame occurrence).environment
          raw := (originalRaw seed frame occurrence).expression
          state := endpoint seed frame occurrence
          owner := RootGeneratedDebtActivationJointSource.OwnerFree.mathEntry (original seed frame) current
            (originalReader seed frame occurrence) (endpoint seed frame occurrence) }
abbrev actualRequest := requestMaterial seed frame occurrence
  ((calculationRoot seed frame occurrence).emitted (endpoint seed frame occurrence))
abbrev nativeInput := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (actualRequest seed frame occurrence)
abbrev expression := (nativeInput seed frame occurrence).expression
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
  ⟨(nativeInput seed frame occurrence).environment,(nativeInput seed frame occurrence).expression⟩
def material := (Pair.material seed frame occurrence,sourceResult seed frame occurrence,raw seed frame occurrence)
def liftEvent : CofinalHistorySettlement.PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort) →
    CofinalHistorySettlement.PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort)
  | .generator expression => .generator (liftExpr expression)
  | .relation word => .relation (liftMap (R:=ℤ) word)

def liftedInventory := (updatedSeed seed frame occurrence).map liftEvent

def priorPairInventory := match frame.pairInventory with
  | none => liftedInventory seed frame occurrence
  | some carried => SourceHistoryCommon.seed carried (liftedInventory seed frame occurrence)

def pairInventory := SourceHistoryCommon.seed (priorPairInventory seed frame occurrence)
  (SourceOperationPaidRelations.exposure (sourceResult seed frame occurrence).2.1.2)

def sourceComponent : SourceNativeProjectionLaw
    (Mother.baseState {frame with depth:=0}).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1} ⊕ PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} supplied _ => match projection with
    | .inl _ => type_of% (material seed frame supplied)
    | .inr _ => type_of% (pairInventory seed frame supplied)
  project := fun projection {_current} supplied _ => match projection with
    | .inl _ => material seed frame supplied
    | .inr _ => pairInventory seed frame supplied

def sourceReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  ((sourceComponent seed frame).project (.inl PUnit.unit) supplied PUnit.unit).2.2

def configuration : Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) where
  LowVar := PhysicalVar
  datum sourceFrame := { component:=some (sourceComponent seed sourceFrame),reader:=sourceReader seed sourceFrame }
  nextInventory := (programme seed).nextInventory
  nextPairInventory sourceFrame := some (((sourceComponent seed {sourceFrame with depth:=0}).project
    (.inr PUnit.unit) (sourceFrame.currentState.root.emitted sourceFrame.currentState.visit.current) PUnit.unit))

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
