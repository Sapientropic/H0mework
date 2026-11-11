import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Initial
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace AS
export OriginalKMaterialPhysicalStockSourceAction.AS (write template stockCfg)
end AS
namespace WB
export OriginalKMaterialPhysicalStockSourceAction.WB (programme oldPaid nativeAt)
end WB
namespace CF
export OriginalKMaterialPhysicalStockSourceAction.CF (codeAt collapseValue)
end CF
namespace SF
export OriginalKMaterialPhysicalStockSourceAction.SF (Factory Packet)
end SF
namespace A
export OriginalKMaterialPhysicalStockSourceAction.A (Programme)
end A
local instance initEmitterGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def sourceInitialPlus : Prior.Branches →L[ℂ] Prior.Branches :=
 sourceQuarterSlots.comp ((sourceDualPlusRaw t).comp originalField)
def sourceInitialMinus : Prior.Branches →L[ℂ] Prior.Branches :=
 sourceQuarterSlots.comp ((sourceDualMinusRaw t).comp originalField)

/-- Both complete raw inverse feet execute as literal children before the real decoder writes initial slots. -/
def sourceInitCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add
  (.linear (s:=()) (t:=()) sourceInjectTailPlus.toLinearMap.toAddMonoidHom
   (.linear (s:=()) (t:=()) (sourceInitialPlus t).toLinearMap.toAddMonoidHom (.var ())))
  (.linear (s:=()) (t:=()) sourceInjectTailMinus.toLinearMap.toAddMonoidHom
   (.linear (s:=()) (t:=()) (sourceInitialMinus t).toLinearMap.toAddMonoidHom (.var ())))

theorem source_init_code_read (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceInitCode t).eval environment=sourceInitialSlots t (environment () ()) := by
 change ((0,0),(OriginalKCvelSourceAction.actualStockExtension (sourceDualPlusRaw t (originalField (environment () ()))),0))+
  ((0,0),(0,OriginalKCvelSourceAction.actualStockExtension (sourceDualMinusRaw t (originalField (environment () ())))))=_
 apply Prod.ext
 · apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,zero_add] <;> rfl
 · apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,zero_add,add_zero] <;> rfl

def actualSourceSlotWrite (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 Env (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar := by
 let installed : Expr (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar () :=
   language.symm ▸ CF.codeAt code grade
 exact fun target _name => by
  cases target
  exact installed.eval (AS.write factory grade data sourceCfg language value)

/-- The existing source decoder writes actual oldPaid + nativeAt through source initialization. No next-slot result is a constructor input. -/
def sourceSlotInitBase :=
 { AS.template factory grade data sourceCfg language with
  datum := fun currentFrame => { (AS.template factory grade data sourceCfg language).datum currentFrame with
   nextEnvironmentReadAt :=
    ((WB.programme data.1 sourceCfg (actualSourceSlotWrite factory grade data sourceCfg language (sourceInitCode t))).datum currentFrame).nextEnvironmentReadAt } }

def sourceSlotInitProgramme := AS.stockCfg (sourceSlotInitBase t factory grade data sourceCfg language)

/-- Current calculation reads the literal tail-driven successor. Its environment decoder is installed separately by the actual source factory. -/
def actualSourceSlotSuccessorFactory :=
 OriginalKFullSourceRAction.AI.withActualInput sourceNextSlotsCode factory

theorem source_slot_init_decoder (currentFrame) :
 ((sourceSlotInitProgramme t factory grade data sourceCfg language).datum currentFrame).nextEnvironmentReadAt =
 some (fun {_current} supplied _paid => actualSourceSlotWrite factory grade data sourceCfg language (sourceInitCode t)
  (WB.oldPaid data.1 sourceCfg+WB.nativeAt sourceCfg currentFrame supplied)) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
