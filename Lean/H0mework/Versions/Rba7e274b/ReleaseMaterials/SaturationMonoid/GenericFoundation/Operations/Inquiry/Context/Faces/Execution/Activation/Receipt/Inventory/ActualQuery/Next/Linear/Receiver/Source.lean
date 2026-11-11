import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Next.Linear.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace FullSourceReceiverLinearAction
-- Only the source-generated receiver epoch changes; other datum entries retain the original reader.
section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Next
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next (receiver)
end Next
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (commonInstalled commonMaterial programme)
end Q
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence)
end I
namespace C
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current originalOccurrence)
end C
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
variable {current : C.Current (Next.receiver frame cfg).registered}
variable (supplied : I.Occurrence (Next.receiver frame cfg) (current := current))

def receiverCommonAt :=
 (Next.receiver frame cfg).old.root.source.base.projectionLaw.project
  ((Q.commonInstalled frame cfg).embed PUnit.unit)
  (C.originalOccurrence (Next.receiver frame cfg).registered (Next.receiver frame cfg).packetAt supplied)
  PUnit.unit

def currentFullRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue Value) (Var := cfg.LowVar) (sort := s) :=
 (receiverCommonAt frame cfg supplied).2.1

theorem current_native_source : currentFullRaw frame cfg supplied =
 (Q.commonMaterial (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) cfg
  (C.originalOccurrence (Next.receiver frame cfg).registered (Next.receiver frame cfg).packetAt supplied)).2.1 := rfl

end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum epoch)
end A
namespace Next
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next (lowProgramme)
end Next
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader)
end R
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
variable (action : PairValue (PairValue Value) s →+ PairValue (PairValue Value) s)
variable {current : C.Current (Next.receiver frame cfg).registered}
variable (supplied : I.Occurrence (Next.receiver frame cfg) (current := current))

def currentLinearRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue Value)) (Var := cfg.LowVar) (sort := s) :=
 ⟨pairEnvironment (currentFullRaw frame cfg supplied).environment 0,
  .linear action (liftExpr (currentFullRaw frame cfg supplied).expression)⟩

def receiverDatum : A.SourceDatum (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar)
 cfg.LowVar (A.epoch (Next.receiver frame cfg)) :=
 { (Next.lowProgramme frame cfg).datum (A.epoch (Next.receiver frame cfg)) with
   calculationReader := some (fun {_current} supplied => currentLinearRaw frame cfg action supplied) }

def lowProgramme : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := s) := by
 classical
 exact { Next.lowProgramme frame cfg with
  datum := Function.update (Next.lowProgramme frame cfg).datum (A.epoch (Next.receiver frame cfg))
   (receiverDatum frame cfg action) }

def programme := Q.programme (lowProgramme frame cfg action)

theorem datum_actual_epoch :
 (lowProgramme frame cfg action).datum (A.epoch (A.epoch (Next.receiver frame cfg))) =
 receiverDatum frame cfg action := by
 classical
 change Function.update (Next.lowProgramme frame cfg).datum (A.epoch (Next.receiver frame cfg))
  (receiverDatum frame cfg action) (A.epoch (Next.receiver frame cfg)) = _
 exact Function.update_self _ _ _

theorem reader_actual_source :
 R.actionReader (Next.receiver frame cfg) (programme frame cfg action) supplied =
 currentLinearRaw frame cfg action supplied := by
 change R.actionReader (A.epoch (Next.receiver frame cfg)) (lowProgramme frame cfg action) supplied = _
 unfold R.actionReader SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
 rw [datum_actual_epoch]
 rfl

end

end FullSourceReceiverLinearAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
