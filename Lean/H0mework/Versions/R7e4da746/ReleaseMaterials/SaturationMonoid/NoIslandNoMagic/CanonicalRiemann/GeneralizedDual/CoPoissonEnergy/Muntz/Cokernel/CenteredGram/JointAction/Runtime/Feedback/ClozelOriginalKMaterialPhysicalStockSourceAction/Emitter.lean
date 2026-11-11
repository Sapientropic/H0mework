import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace AS
export OriginalKFinitePaWindowOperatorSourceAction.AS (write template stockCfg)
end AS
namespace CF
export OriginalKFinitePaWindowOperatorSourceAction.CF (codeAt collapseValue)
end CF
namespace WB
export OriginalKFinitePaWindowOperatorSourceAction.WB (programme oldPaid nativeAt)
end WB
namespace T
export OriginalKFinitePaWindowOperatorSourceAction.T (preserve)
end T
namespace S
export OriginalKFinitePaWindowOperatorSourceAction.S (actualOccurrence)
end S
local instance physicalEmitterGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (N : ℕ)

def physicalStockWriteCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .add (.var ()) (physicalStockCode N)

/-- The write action keeps the complete incoming material; its physical stock is a new generated output role. -/
def physicalStockWrite (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
    Env (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar := by
  let code : Expr (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar () :=
    language.symm ▸ CF.codeAt (physicalStockWriteCode N) grade
  exact fun target _ => by
    cases target
    exact code.eval (AS.write factory grade data sourceCfg language value)

def physicalStockEmitterBase :=
 { AS.template factory grade data sourceCfg language with
   datum := fun frame => { (AS.template factory grade data sourceCfg language).datum frame with
    nextEnvironmentReadAt :=
     ((WB.programme data.1 sourceCfg (physicalStockWrite factory grade data sourceCfg language N)).datum frame).nextEnvironmentReadAt } }

abbrev MaterialFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=())

def physicalSourceRaw (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (frame : MaterialFrame grade sourceCfg) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=()) :=
  OriginalKFinitePaWindowOperatorSourceAction.sourceLiteralRaw factory grade data sourceCfg language code frame

def physicalSourceTrace (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (frame : MaterialFrame grade sourceCfg) :
    Trace (physicalSourceRaw factory grade data sourceCfg language code frame).environment
      (physicalSourceRaw factory grade data sourceCfg language code frame).expression
      (.const ((physicalSourceRaw factory grade data sourceCfg language code frame).expression.eval
        (physicalSourceRaw factory grade data sourceCfg language code frame).environment)) := execution _ _

def physicalSourceInventory (frame : MaterialFrame grade sourceCfg) :=
  SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure
    (physicalSourceTrace factory grade data sourceCfg language (.var ()) frame))
   (SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure
    (physicalSourceTrace factory grade data sourceCfg language (physicalStockCode N) frame))
    (SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure
     (physicalSourceTrace factory grade data sourceCfg language (physicalTailCode N) frame))
     (SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure
      (physicalSourceTrace factory grade data sourceCfg language physicalProjectionCode frame))
      (SourceOperationPaidRelations.exposure
       (physicalSourceTrace factory grade data sourceCfg language (physicalStockWriteCode N) frame)))))

def physicalStockEmitter :=
 { physicalStockEmitterBase factory grade data sourceCfg language N with
   nextInventory := fun frame => some (T.preserve
    ((physicalStockEmitterBase factory grade data sourceCfg language N).nextInventory frame)
    (physicalSourceInventory factory grade data sourceCfg language N frame)) }

theorem physical_stock_decoder_installed (frame : MaterialFrame grade sourceCfg) :
 ((physicalStockEmitter factory grade data sourceCfg language N).datum frame).nextEnvironmentReadAt =
 some (fun {_current} supplied _paid => physicalStockWrite factory grade data sourceCfg language N
  (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame supplied)) := rfl

theorem physical_stock_inventory_installed (frame : MaterialFrame grade sourceCfg) :
 (physicalStockEmitter factory grade data sourceCfg language N).nextInventory frame =
 some (T.preserve ((physicalStockEmitterBase factory grade data sourceCfg language N).nextInventory frame)
  (physicalSourceInventory factory grade data sourceCfg language N frame)) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
