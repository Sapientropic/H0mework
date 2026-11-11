import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Material.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Transport
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Inventory.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.PairTransport
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
end A
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next actualOccurrence)
end Q
namespace M
export SourceGeneratedInquiryReceiptAction.Configured.Material (programme initial selected born)
end M
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (priorPairInventory pairInventory liftedInventory raw)
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (completeWrittenInventory disposition)
namespace G
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated
 (writtenInventory completeWrittenInventory)
end G
end J
end P

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X s)))
variable (frame : A.M.Frame (Value := V) (Var := X) (sort := s))
variable (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue V) X s)))
variable (hasPrior : frame.pairInventory = some prior)

def priorSegment : SourceInventoryTraceSegment prior
    (P.pairInventory seed (A.epoch frame) (Q.actualOccurrence frame)) := by
  apply SourceInventoryTraceSegment.trans (middle :=
    P.priorPairInventory seed (A.epoch frame) (Q.actualOccurrence frame))
  · change SourceInventoryTraceSegment prior
      (match frame.pairInventory with
       | none => P.liftedInventory seed (A.epoch frame) (Q.actualOccurrence frame)
       | some carried => SourceHistoryCommon.seed carried
           (P.liftedInventory seed (A.epoch frame) (Q.actualOccurrence frame)))
    rw [hasPrior]
    exact .left _ _
  · exact .left _ _

def dispositionSegment : SourceInventoryTraceSegment
    (P.pairInventory seed (A.epoch frame) (Q.actualOccurrence frame))
    (P.J.completeWrittenInventory seed (A.epoch frame) (Q.actualOccurrence frame)) := by
  apply SourceInventoryTraceSegment.trans (middle := P.J.G.writtenInventory seed
    (A.epoch frame) (Q.actualOccurrence frame) (P.raw seed (A.epoch frame) (Q.actualOccurrence frame))
      (P.J.disposition seed (A.epoch frame) (Q.actualOccurrence frame)))
  · unfold P.J.G.writtenInventory
    cases P.J.disposition seed (A.epoch frame) (Q.actualOccurrence frame) with
    | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => exact .refl _
    | kernelResidual _ _ _ => exact .left _ _
  · exact .left _ _

def writtenSegment : SourceInventoryTraceSegment prior
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.written
      seed frame) :=
  ((priorSegment seed frame prior hasPrior).trans (dispositionSegment seed frame)).trans (.right _ _)

variable (cfg : A.Programme (PhysicalValue := V) (PhysicalVar := X) (sort := s))
variable (write : PairValue V s → Env (PairValue V) cfg.LowVar)

theorem selected_pair_inventory :
    (M.selected frame cfg (Writeback.programme frame cfg write)).pairInventory =
      some (lowPairWritten frame cfg) := by
  apply SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix.receipt_read
    (M.programme frame cfg (Writeback.programme frame cfg write)) (M.initial frame cfg)
    (fun stage => (Q.frames (M.initial frame cfg)
      (M.programme frame cfg (Writeback.programme frame cfg write)) stage).pairInventory)
  intro stage paid actual
  have step : Q.frames (M.initial frame cfg) (M.programme frame cfg (Writeback.programme frame cfg write)) (stage+1) =
      (Q.frames (M.initial frame cfg) (M.programme frame cfg (Writeback.programme frame cfg write)) stage).mathNext := by
    change Q.next _ _ = _
    unfold Q.next
    rw [actual]
  exact (congrArg (fun candidate : A.M.Frame (Value := PairValue V) (Var := cfg.LowVar) (sort := s) =>
    candidate.pairInventory) step).trans rfl

def bornPairInventory :=
  let selected := M.selected frame cfg (Writeback.programme frame cfg write)
  let seed := lowSeed frame cfg
  SourceHistoryCommon.seed
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.written seed selected)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Inverse.paidWritten
      seed (A.epoch selected) (Q.actualOccurrence selected))

theorem born_pair_inventory :
    (M.born frame cfg (Writeback.programme frame cfg write)).pairInventory =
      some (bornPairInventory frame cfg write) := rfl

def bornSegment : SourceInventoryTraceSegment (lowPairWritten frame cfg) (bornPairInventory frame cfg write) :=
  (writtenSegment (lowSeed frame cfg) (M.selected frame cfg (Writeback.programme frame cfg write))
    (lowPairWritten frame cfg) (selected_pair_inventory frame cfg write)).trans (.left _ _)

end SourceGeneratedInquiryReceiptAction.Configured.PairTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
