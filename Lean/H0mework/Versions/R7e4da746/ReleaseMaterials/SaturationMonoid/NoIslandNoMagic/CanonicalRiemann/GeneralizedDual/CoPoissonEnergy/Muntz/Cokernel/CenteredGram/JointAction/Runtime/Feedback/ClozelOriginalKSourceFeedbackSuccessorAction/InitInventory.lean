import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitEmitter
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedDualForcingSourceAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace TraceSource
export OriginalKMaterialPhysicalStockSourceAction (physicalSourceRaw physicalSourceTrace)
end TraceSource
namespace Stock
export OriginalKMaterialPhysicalStockSourceAction.T (preserve)
end Stock
local instance initInventoryGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

/-- Same original total's full raw fields and mean debt execute before the output changes to raw feedback slots. -/
def sourceInitMeanCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) (OriginalKExpandedDualForcingSourceAction.sourceMeanDebtMaterialAction t).toLinearMap.toAddMonoidHom (.var ())

def sourceInitInventoryCodes : List (Expr (PairValue (PairValue C.Value)) C.Var ()) :=
 [.var (),sourceInitCode t,sourceInitMeanCode t]

def sourceInitQueryTrace (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (frame) :=
 TraceSource.physicalSourceTrace factory grade data sourceCfg language code frame

def sourceInitQueryPairTrace (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (frame) :
 Trace (pairEnvironment (TraceSource.physicalSourceRaw factory grade data sourceCfg language code frame).environment 0)
 (liftExpr (TraceSource.physicalSourceRaw factory grade data sourceCfg language code frame).expression)
 (.const ((liftExpr (TraceSource.physicalSourceRaw factory grade data sourceCfg language code frame).expression).eval
  (pairEnvironment (TraceSource.physicalSourceRaw factory grade data sourceCfg language code frame).environment 0))) := execution _ _

/-- Original full source, inherited word, literal inverse raw feet and mean debt all belong to this same source initialization occurrence. -/
def sourceSlotInitStockBase :=
 { sourceSlotInitBase t factory grade data sourceCfg language with
  nextInventory := fun frame => (sourceInitInventoryCodes t).foldl
   (fun prior code => some (Stock.preserve prior (SourceOperationPaidRelations.exposure
    (sourceInitQueryTrace factory grade data sourceCfg language code frame))))
   ((sourceSlotInitBase t factory grade data sourceCfg language).nextInventory frame),
  nextPairInventory := fun frame => (sourceInitInventoryCodes t).foldl
   (fun prior code => some (Stock.preserve prior (SourceOperationPaidRelations.exposure
    (sourceInitQueryPairTrace factory grade data sourceCfg language code frame))))
   ((sourceSlotInitBase t factory grade data sourceCfg language).nextPairInventory frame) }

theorem source_init_stock_decoder_same : (sourceSlotInitStockBase t factory grade data sourceCfg language).datum=
 (sourceSlotInitBase t factory grade data sourceCfg language).datum := rfl
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
