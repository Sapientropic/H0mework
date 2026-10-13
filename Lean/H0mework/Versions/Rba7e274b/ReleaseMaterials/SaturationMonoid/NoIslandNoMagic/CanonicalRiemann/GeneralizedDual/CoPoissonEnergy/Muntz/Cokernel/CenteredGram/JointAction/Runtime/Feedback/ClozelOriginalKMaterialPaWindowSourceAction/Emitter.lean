import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace AS
export OriginalKWholePaNativeRankSourceUpdate.SourceAS (write template stockCfg)
end AS
namespace CF
export OriginalKWholePaNativeRankSourceUpdate.SourceCF (codeAt)
end CF
namespace WB
export OriginalKWholePaNativeRankSourceUpdate.SourceWB (programme oldPaid nativeAt)
end WB
namespace T
export OriginalKWholePaNativeRankSourceUpdate.ActorStock (preserve)
end T
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
local instance paEmitterGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def sourcePaStockCode (source : D.SourceBranches) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.var ()) (.linear (s:=()) (t:=()) sourcePaSourceAction.toLinearMap.toAddMonoidHom (.const source))

theorem source_pa_stock_code (source : D.SourceBranches) (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourcePaStockCode source).eval environment = environment () () + sourcePaSourceAction source := rfl

def sourcePaStockWrite (source : D.SourceBranches)
 (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 Env (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar := by
 let code : Expr (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar () :=
  language.symm ▸ CF.codeAt (sourcePaStockCode source) grade
 exact fun target _ => by
  cases target
  exact code.eval (AS.write factory grade data sourceCfg language value)

def sourcePaEmitterBase (source : D.SourceBranches) :=
 { AS.template factory grade data sourceCfg language with
   datum := fun frame => { (AS.template factory grade data sourceCfg language).datum frame with
    nextEnvironmentReadAt :=
     ((WB.programme data.1 sourceCfg (sourcePaStockWrite factory grade data sourceCfg language source)).datum frame).nextEnvironmentReadAt } }

abbrev SourcePaFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=())

def sourcePaStockRaw (source : D.SourceBranches) (frame : SourcePaFrame grade sourceCfg) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=()) :=
 ⟨AS.write factory grade data sourceCfg language
   (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame (S.actualOccurrence frame)),
  language.symm ▸ CF.codeAt (sourcePaStockCode source) grade⟩

def sourcePaStockTrace (source : D.SourceBranches) (frame : SourcePaFrame grade sourceCfg) :
 Trace (sourcePaStockRaw factory grade data sourceCfg language source frame).environment
  (sourcePaStockRaw factory grade data sourceCfg language source frame).expression
  (.const ((sourcePaStockRaw factory grade data sourceCfg language source frame).expression.eval
   (sourcePaStockRaw factory grade data sourceCfg language source frame).environment)) := execution _ _

def sourcePaStockInventory (source : D.SourceBranches) (frame : SourcePaFrame grade sourceCfg) :=
 SourceOperationPaidRelations.exposure (sourcePaStockTrace factory grade data sourceCfg language source frame)

def sourcePaEmitterStock (source : D.SourceBranches) :=
 { sourcePaEmitterBase factory grade data sourceCfg language source with
   nextInventory := fun frame => some (T.preserve
    ((sourcePaEmitterBase factory grade data sourceCfg language source).nextInventory frame)
    (sourcePaStockInventory factory grade data sourceCfg language source frame)) }

theorem source_pa_stock_decoder_installed (source : D.SourceBranches) (frame : SourcePaFrame grade sourceCfg) :
 ((sourcePaEmitterStock factory grade data sourceCfg language source).datum frame).nextEnvironmentReadAt =
 some (fun {_current} supplied _paid => sourcePaStockWrite factory grade data sourceCfg language source
  (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame supplied)) := rfl

theorem source_pa_stock_inventory_installed (source : D.SourceBranches) (frame : SourcePaFrame grade sourceCfg) :
 (sourcePaEmitterStock factory grade data sourceCfg language source).nextInventory frame =
 some (T.preserve ((sourcePaEmitterBase factory grade data sourceCfg language source).nextInventory frame)
  (sourcePaStockInventory factory grade data sourceCfg language source frame)) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
