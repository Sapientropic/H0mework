import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.Factory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance traceFactoryGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (grade : Nat)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=L.Value W grade) (Var:=X) (sort:=()))

/-- Actual registered-source environmental and syntax nodes share the same original supplied query. -/
def sourceMaterialAuxCodes : List (Expr (PairValue (L.Value W grade)) X ()) :=
 let supplied:=S.actualOccurrence frame
 let material:=I.materialAt (A.epoch frame) supplied
 [sourceMaterialCode (A.epoch frame) supplied,
  liftExpr material.raw.expression,
  liftExpr (sourceRawDeltaTerm material.raw material.nextRaw)]

def sourceMaterialAuxEnvironment := sourceMaterialEnvironment (A.epoch frame) (S.actualOccurrence frame)

def sourceMaterialAuxTrace (code : Expr (PairValue (L.Value W grade)) X ()) :=
 execution (sourceMaterialAuxEnvironment grade frame) code

def sourceMaterialAuxPairTrace (code : Expr (PairValue (L.Value W grade)) X ()) :=
 execution (pairEnvironment (sourceMaterialAuxEnvironment grade frame) 0) (liftExpr code)

/-- Existing scalar/pair source stock stays; all literal environment/syntax faces are installed before the source native receiver. -/
def sourceDifferentialTraceFactory (mother : SF.Factory W X ()) : SF.Factory W X () :=
 {mother with
  extraScalar:=fun n seed currentFrame=>
   (sourceMaterialAuxCodes n currentFrame).foldl (fun prior code=>some (Stock.preserve prior
    (SourceOperationPaidRelations.exposure (sourceMaterialAuxTrace n currentFrame code))))
    (mother.extraScalar n seed currentFrame),
  extraPair:=fun n seed currentFrame=>
   (sourceMaterialAuxCodes n currentFrame).foldl (fun prior code=>some (Stock.preserve prior
    (SourceOperationPaidRelations.exposure (sourceMaterialAuxPairTrace n currentFrame code))))
    (mother.extraPair n seed currentFrame)}

/-- Installing the extra source faces preserves the actual reader/decoder programme and normal next stock. -/
theorem source_differential_trace_keeps (mother : SF.Factory W X ()) :
 (sourceDifferentialTraceFactory mother).datum=mother.datum ∧
 (sourceDifferentialTraceFactory mother).nextInventory=mother.nextInventory ∧
 (sourceDifferentialTraceFactory mother).nextPairInventory=mother.nextPairInventory := ⟨rfl,rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
