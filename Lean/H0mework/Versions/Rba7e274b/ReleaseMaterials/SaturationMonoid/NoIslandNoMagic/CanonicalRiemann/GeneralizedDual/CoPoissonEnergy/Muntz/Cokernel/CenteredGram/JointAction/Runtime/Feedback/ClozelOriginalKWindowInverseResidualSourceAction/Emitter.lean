import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace F
export OriginalKFinitePaWindowOperatorSourceAction (Branches firstInverseAction completeWindowWord finite_word_source_value windowEnvironment)
end F
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace Native
export OriginalKBoundaryNativeSourceAction (sourceFields source_fields_first)
end Native


namespace SF
export OriginalKFinitePaWindowOperatorSourceAction.SF (Factory Packet)
end SF
namespace A
export OriginalKFinitePaWindowOperatorSourceAction.A (Programme)
end A
namespace L
export OriginalKFinitePaWindowOperatorSourceAction.L (Value groups)
end L
namespace AS
export OriginalKFinitePaWindowOperatorSourceAction.AS (write template stockCfg)
end AS
namespace CF
export OriginalKFinitePaWindowOperatorSourceAction.CF (codeAt collapseValue code_base_value)
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
local instance residualEmitterGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)
variable (radius : ℝ) (source residual : F.Branches)

def residualStockWrite (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 Env (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar := by
 let code : Expr (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar () :=
  language.symm ▸ CF.codeAt (residualStockCode radius source residual) grade
 exact fun target _ => by
  cases target
  exact code.eval (AS.write factory grade data sourceCfg language value)

def residualEmitterBase :=
 { AS.template factory grade data sourceCfg language with
   datum := fun frame => { (AS.template factory grade data sourceCfg language).datum frame with
    nextEnvironmentReadAt :=
     ((WB.programme data.1 sourceCfg (residualStockWrite factory grade data sourceCfg language radius source residual)).datum frame).nextEnvironmentReadAt } }

abbrev ResidualFrame := OriginalKFinitePaWindowOperatorSourceAction.SourcePaFrame grade sourceCfg

def residualStockRaw (frame : ResidualFrame grade sourceCfg) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=()) :=
 OriginalKFinitePaWindowOperatorSourceAction.sourceLiteralRaw factory grade data sourceCfg language
  (residualStockCode radius source residual) frame

def residualStockTrace (frame : ResidualFrame grade sourceCfg) :
 Trace (residualStockRaw factory grade data sourceCfg language radius source residual frame).environment
  (residualStockRaw factory grade data sourceCfg language radius source residual frame).expression
  (.const ((residualStockRaw factory grade data sourceCfg language radius source residual frame).expression.eval
   (residualStockRaw factory grade data sourceCfg language radius source residual frame).environment)) := execution _ _

/-- The original forward/inverse/two-mean/cochain stock stays in the same source inventory. -/
def residualStockInventory (frame : ResidualFrame grade sourceCfg) :=
 SourceHistoryCommon.seed
  (OriginalKFinitePaWindowOperatorSourceAction.finiteStockInventory factory grade data sourceCfg language radius source frame)
  (SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure
   (residualStockTrace factory grade data sourceCfg language radius source residual frame))
   (OriginalKFinitePaWindowOperatorSourceAction.sourceLiteralInventory factory grade data sourceCfg language
    (residualCorrectionCode source residual) frame))

def residualEmitterStock :=
 { residualEmitterBase factory grade data sourceCfg language radius source residual with
   nextInventory := fun frame => some (T.preserve
    ((residualEmitterBase factory grade data sourceCfg language radius source residual).nextInventory frame)
    (residualStockInventory factory grade data sourceCfg language radius source residual frame)) }

theorem residual_decoder_installed (frame : ResidualFrame grade sourceCfg) :
 ((residualEmitterStock factory grade data sourceCfg language radius source residual).datum frame).nextEnvironmentReadAt =
 some (fun {_current} supplied _paid => residualStockWrite factory grade data sourceCfg language radius source residual
  (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg frame supplied)) := rfl

theorem residual_inventory_installed (frame : ResidualFrame grade sourceCfg) :
 (residualEmitterStock factory grade data sourceCfg language radius source residual).nextInventory frame =
 some (T.preserve ((residualEmitterBase factory grade data sourceCfg language radius source residual).nextInventory frame)
  (residualStockInventory factory grade data sourceCfg language radius source residual frame)) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
