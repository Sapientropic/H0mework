import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalActionWrite.Inventory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalActionWrite.Whole
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalActionWrite.Received
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackContinuationAction
 (actualCurrentSourceFactory actualCurrentSourceData actualCurrentSourceBase continuationSourceStockEmitter continuationSourceBorn)
end Parent
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket bornAfterNative receiver nextSeed localNativeReceipt stockCfg)
end AS

namespace AN
export ActualNativeRelationTransport (paid)
end AN
namespace Pay
export SourceFamilyActualCurrentMaterialRootedEffect (BornWholeWrite bornWholeWrite)
end Pay
local instance materialFamilyGroups {W : Unit → Type} [∀ target,AddCommGroup (W target)]
 (grade : Nat) (target : Unit) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable {W X : Unit → Type} [∀ target,AddCommGroup (W target)]
variable (literalCode : Expr (PairValue W) X ()) (factory : SF.Factory W X ())
variable (incoming : AP.AdmissionPacket (W:=W) (X:=X) (s:=()))

/-- The actual native whole is the paid source packet's existing birth, on its original source occurrence. -/
def sourceNativeWhole : Pay.BornWholeWrite (sourceNativeSelected literalCode factory incoming)
 (sourceNativePacket literalCode factory incoming).2.2.1 := Pay.bornWholeWrite _ _

/-- The registered current residual is read from the same actual born whole, separately from its active source write. -/
def sourceNativeRegisteredValue : PairValue (L.Value W incoming.1) () :=
 (sourceNativeBorn literalCode factory incoming).2.1.1.registered.input.expression.eval
  (sourceNativeBorn literalCode factory incoming).2.1.1.registered.input.environment

/-- This endpoint comes from the source's real completion receipt. -/
theorem source_native_material_endpoint :
 (AN.paid (sourceNativeSelected literalCode factory incoming)).state.1=
 .const (Native.nativeValue (sourceCofinalFactory literalCode factory)
  (sourceActionPacket literalCode factory incoming)) :=
 (sourceNativeReceipt literalCode factory incoming).2.1.2.down

/-- The existing whole's environment/expression fields generate the material effect at this receipt. -/
theorem source_native_whole_registered_effect :
 sourceNativeRegisteredValue literalCode factory incoming=
 (AN.paid (sourceNativeSelected literalCode factory incoming)).raw.effect
  (AN.paid (sourceNativeSelected literalCode factory incoming)).environment
  (AN.paid (sourceNativeSelected literalCode factory incoming)).increment :=
 OriginalKMaterialPhysicalStockSourceAction.whole_registered_native_effect
  (sourceNativeSelected literalCode factory incoming)
  (sourceNativePacket literalCode factory incoming).2.2.1
  (sourceNativeWhole literalCode factory incoming) _
  (source_native_material_endpoint literalCode factory incoming)

private theorem paid_endpoint_update
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (value : Value ()) (endpoint : (AN.paid frame).state.1=.const value) :
 value+(AN.paid frame).raw.effect (AN.paid frame).environment (AN.paid frame).increment=
 (AN.paid frame).raw.eval ((AN.paid frame).environment+(AN.paid frame).increment) := by
 have paid := (AN.paid frame).state.2.sound
 rw [endpoint] at paid
 simp only [Expr.eval] at paid
 rw [Expr.eval_update,paid]

/-- The complete actual update retains both the generated receipt endpoint and the registered residual. -/
theorem source_native_material_updated_value :
 (show PairValue (L.Value W incoming.1) () from
  Native.nativeValue (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory incoming))+
 sourceNativeRegisteredValue literalCode factory incoming=
 (show PairValue (L.Value W incoming.1) () from
  (AN.paid (sourceNativeSelected literalCode factory incoming)).raw.eval
   ((AN.paid (sourceNativeSelected literalCode factory incoming)).environment+
    (AN.paid (sourceNativeSelected literalCode factory incoming)).increment)) := by
 rw [source_native_whole_registered_effect]
 exact paid_endpoint_update _ _ (source_native_material_endpoint literalCode factory incoming)

/-- The independent whole reader reconstructs the source writer total from its complete material update and actual registered residual. -/
def sourceNativeWholeTotal : PairValue (L.Value W incoming.1) () :=
 WB.oldPaid incoming.2.1.1 (sourceCofinalCfg literalCode factory incoming.1 incoming.2.1.2)+
 ((show PairValue (L.Value W incoming.1) () from
   (AN.paid (sourceNativeSelected literalCode factory incoming)).raw.eval
    ((AN.paid (sourceNativeSelected literalCode factory incoming)).environment+
     (AN.paid (sourceNativeSelected literalCode factory incoming)).increment))-
  sourceNativeRegisteredValue literalCode factory incoming)

/-- Both material fees are consumed before the literal source action is read. -/
theorem source_native_whole_total_code :
 sourceNativeWholeTotal literalCode factory incoming=
 (CF.codeAt literalCode incoming.1).eval
  (N.input (R.actualMaterial incoming.2.1.1
   (sourceCofinalCfg literalCode factory incoming.1 incoming.2.1.2))).environment := by
 unfold sourceNativeWholeTotal
 rw [←source_native_material_updated_value,add_sub_cancel_right]
 exact source_native_actual_total literalCode factory incoming

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
