import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.Reentry.Splice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Origin
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceInventoryExecutionFeed
namespace T
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action (sourceAction code full_source_action code_effect)
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.F (BaseValue)
namespace C
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.F.C (Value Var)
end C
end F
namespace DR
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.DR (completeRSourceRead)
namespace L
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.DR.L (Value groups)
end L
end DR
namespace P
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.P (R)
end P
namespace Two
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.Two (totalBranches)
end Two
namespace Ret
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.Ret (pairedPacking)
end Ret
end T
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
 (OriginMaterialAt afterEnvironment material sourceOccurrence sourceWord words raw)
end SN
namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice (originFace origin_retained)
end SP
namespace Ctx
export SourceInventoryExecutionFeed.SourceWordNative.Reentry (completedOriginFace)
namespace A
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.A (Programme)
namespace M
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.A.M (Frame)
end M
end A
namespace AS
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.AS (stockScalar)
end AS
end Ctx

local instance baseGroups (n : Nat) : ∀ t, AddCommGroup (T.F.BaseValue n t) := T.DR.L.groups (PairValue T.F.C.Value) n
local instance originGroups (n : Nat) : ∀ t,AddCommGroup (T.DR.L.Value (T.F.BaseValue n) 2 t) := T.DR.L.groups (T.F.BaseValue n) 2
local instance runtimeGroups (n : Nat) : ∀ t,AddCommGroup
 (T.DR.L.Value (T.DR.L.Value (T.F.BaseValue n) 2) 0 t) := T.DR.L.groups (T.DR.L.Value (T.F.BaseValue n) 2) 0
local instance codeGroups (n : Nat) : ∀ t,AddCommGroup
 (PairValue (PairValue (PairValue (T.F.BaseValue n))) t) := T.DR.L.groups (T.F.BaseValue n) 3

variable (initial : Nat)
variable (frame : Ctx.A.M.Frame (Value := PairValue (T.F.BaseValue initial)) (Var := T.F.C.Var) (sort := ()))
variable (base : Ctx.A.Programme (PhysicalValue := PairValue (T.F.BaseValue initial)) (PhysicalVar := T.F.C.Var) (sort := ()))
variable (before : Inventory (V := T.F.BaseValue initial) (X := T.F.C.Var) (s := ()))
variable (oldEnvironment : Env (T.F.BaseValue initial) T.F.C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Ctx.AS.stockScalar frame base)))

/-- This is the preserved original source occurrence, not the inventory query result. -/
abbrev origin := (SP.originFace frame base before oldEnvironment admissions).rootRead.source

def sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue (T.F.BaseValue initial))) (Var := T.F.C.Var) (sort := ()) :=
 let source := origin initial frame base before oldEnvironment admissions
 ⟨pairEnvironment source.native.environment 0, liftExpr source.native.raw⟩

def sourceUpdated : Env (PairValue (PairValue (T.F.BaseValue initial))) T.F.C.Var :=
 let source := origin initial frame base before oldEnvironment admissions
 pairEnvironment (source.native.environment+source.native.increment) 0

theorem origin_updated :
 (origin initial frame base before oldEnvironment admissions).native.environment+
 (origin initial frame base before oldEnvironment admissions).native.increment = SN.afterEnvironment frame base :=
 add_sub_cancel _ _

def sourceTrace : type_of% (origin initial frame base before oldEnvironment admissions).newTrace :=
 (origin initial frame base before oldEnvironment admissions).newTrace

theorem source_raw_read :
 (sourceRaw initial frame base before oldEnvironment admissions).expression.eval
  (sourceUpdated initial frame base before oldEnvironment admissions) =
 ((origin initial frame base before oldEnvironment admissions).native.raw.eval (SN.afterEnvironment frame base),0) := by
 change (liftExpr _).eval (pairEnvironment _ 0) = _
 rw [eval_liftExpr,Expr.effect_zero,origin_updated]

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def sourceCode := T.code observation nontrivial half initial
 (sourceRaw initial frame base before oldEnvironment admissions)

def sourceEnvironment := pairEnvironment
 (sourceRaw initial frame base before oldEnvironment admissions).environment
 (sourceUpdated initial frame base before oldEnvironment admissions-
  (sourceRaw initial frame base before oldEnvironment admissions).environment)

/-- The same actual source raw supplies all four branches before the R action. -/
theorem original_source_action :
 T.DR.completeRSourceRead initial 2 0
  ((sourceCode initial frame base before oldEnvironment admissions observation nontrivial half).eval
   (sourceEnvironment initial frame base before oldEnvironment admissions)) =
 T.Ret.pairedPacking (T.P.R observation nontrivial half (T.Two.totalBranches
  (T.DR.completeRSourceRead initial 2 0
   (((origin initial frame base before oldEnvironment admissions).native.raw.eval
     (SN.afterEnvironment frame base),0),0)))) := by
 have actual := T.full_source_action observation nontrivial half initial
  (sourceRaw initial frame base before oldEnvironment admissions)
  (sourceUpdated initial frame base before oldEnvironment admissions)
 rw [source_raw_read] at actual
 exact actual

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Origin
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
