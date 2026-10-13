import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Cochain
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace SF
export OriginalKMaterialPaWindowSourceAction.SF (Factory Packet)
end SF
namespace A
export OriginalKMaterialPaWindowSourceAction.A (Programme)
end A
namespace L
export OriginalKMaterialPaWindowSourceAction.L (Value groups)
end L
namespace AS
export OriginalKMaterialPaWindowSourceAction.AS (write template stockCfg)
end AS
namespace CF
export OriginalKMaterialPaWindowSourceAction.CF (codeAt collapseValue)
end CF
namespace WB
export OriginalKMaterialPaWindowSourceAction.WB (programme oldPaid nativeAt)
end WB
namespace T
export OriginalKMaterialPaWindowSourceAction.T (preserve)
end T
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
local instance finiteEmitterGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def finiteStockWrite (radius : ℝ) (source : Branches)
 (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 Env (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar := by
 let code : Expr (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar () :=
  language.symm ▸ CF.codeAt (sourceStockWord radius source) grade
 exact fun target _ => by
  cases target
  exact code.eval (AS.write factory grade data sourceCfg language value)

def finiteEmitterBase (radius : ℝ) (source : Branches) :=
 { AS.template factory grade data sourceCfg language with
   datum := fun frame => { (AS.template factory grade data sourceCfg language).datum frame with
    nextEnvironmentReadAt :=
     ((WB.programme data.1 sourceCfg (finiteStockWrite factory grade data sourceCfg language radius source)).datum frame).nextEnvironmentReadAt } }

abbrev SourcePaFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=())

def finiteStockRaw (radius : ℝ) (source : Branches) (frame : SourcePaFrame grade sourceCfg) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=()) :=
 ⟨AS.write factory grade data sourceCfg language
   (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame (S.actualOccurrence frame)),
  language.symm ▸ CF.codeAt (sourceStockWord radius source) grade⟩

def finiteStockTrace (radius : ℝ) (source : Branches) (frame : SourcePaFrame grade sourceCfg) :
 Trace (finiteStockRaw factory grade data sourceCfg language radius source frame).environment
  (finiteStockRaw factory grade data sourceCfg language radius source frame).expression
  (.const ((finiteStockRaw factory grade data sourceCfg language radius source frame).expression.eval
   (finiteStockRaw factory grade data sourceCfg language radius source frame).environment)) := execution _ _

def sourceLiteralRaw (expression : Expr (PairValue (PairValue C.Value)) C.Var ())
 (frame : SourcePaFrame grade sourceCfg) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=()) :=
 ⟨AS.write factory grade data sourceCfg language
  (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame (S.actualOccurrence frame)),
  language.symm ▸ CF.codeAt expression grade⟩

def sourceLiteralTrace (expression : Expr (PairValue (PairValue C.Value)) C.Var ())
 (frame : SourcePaFrame grade sourceCfg) :
 Trace (sourceLiteralRaw factory grade data sourceCfg language expression frame).environment
  (sourceLiteralRaw factory grade data sourceCfg language expression frame).expression
  (.const ((sourceLiteralRaw factory grade data sourceCfg language expression frame).expression.eval
   (sourceLiteralRaw factory grade data sourceCfg language expression frame).environment)) := execution _ _

def sourceLiteralInventory (expression : Expr (PairValue (PairValue C.Value)) C.Var ())
 (frame : SourcePaFrame grade sourceCfg) :=
 SourceOperationPaidRelations.exposure (sourceLiteralTrace factory grade data sourceCfg language expression frame)

def sourceFourierPole (radius : ℝ) : Branches →L[ℂ] Branches :=
 Native.sourceFields.comp ((burnolRadiusZeroExtension radius).comp
  ((ContinuousLinearMap.toSpanSingleton ℂ (intervalConstant radius)).comp
   (((-1/2:ℂ) • burnolSourceWindowIntegral).comp OriginalKFullSourceRAction.originalField)))

def finiteStockInventory (radius : ℝ) (source : Branches) (frame : SourcePaFrame grade sourceCfg) :=
 let inherited := CF.collapseValue grade
  (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame (S.actualOccurrence frame))
 let inverse := (inverseResidualWord radius).subst (fun _ _ => .const source)
 let mean : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .linear (s:=()) (t:=()) (sourceFourierPole radius).toLinearMap.toAddMonoidHom (.const source)
 SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure
   (finiteStockTrace factory grade data sourceCfg language radius source frame))
  (SourceHistoryCommon.seed (sourceLiteralInventory factory grade data sourceCfg language inverse frame)
   (SourceHistoryCommon.seed (sourceLiteralInventory factory grade data sourceCfg language mean frame)
    (sourceLiteralInventory factory grade data sourceCfg language (boundCochainWord radius source inherited) frame)))

def finiteEmitterStock (radius : ℝ) (source : Branches) :=
 { finiteEmitterBase factory grade data sourceCfg language radius source with
   nextInventory := fun frame => some (T.preserve
    ((finiteEmitterBase factory grade data sourceCfg language radius source).nextInventory frame)
    (finiteStockInventory factory grade data sourceCfg language radius source frame)) }

theorem finite_stock_decoder_installed (radius : ℝ) (source : Branches) (frame : SourcePaFrame grade sourceCfg) :
 ((finiteEmitterStock factory grade data sourceCfg language radius source).datum frame).nextEnvironmentReadAt =
 some (fun {_current} supplied _paid => finiteStockWrite factory grade data sourceCfg language radius source
  (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame supplied)) := rfl

theorem finite_stock_inventory_installed (radius : ℝ) (source : Branches) (frame : SourcePaFrame grade sourceCfg) :
 (finiteEmitterStock factory grade data sourceCfg language radius source).nextInventory frame =
 some (T.preserve ((finiteEmitterBase factory grade data sourceCfg language radius source).nextInventory frame)
  (finiteStockInventory factory grade data sourceCfg language radius source frame)) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
