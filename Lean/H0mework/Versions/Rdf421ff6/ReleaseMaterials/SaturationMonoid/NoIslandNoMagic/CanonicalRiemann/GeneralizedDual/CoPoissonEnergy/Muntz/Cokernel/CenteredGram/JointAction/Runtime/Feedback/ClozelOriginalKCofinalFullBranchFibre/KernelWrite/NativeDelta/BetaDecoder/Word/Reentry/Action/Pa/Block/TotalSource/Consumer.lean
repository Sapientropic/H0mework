import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Consumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceInventoryExecutionFeed
namespace B
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
 (programme nativeBorn lowBase fullWrite material_raw material_updated physical_action actualCurrent)
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.FC (Value)
end FC
namespace A
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.A (Programme)
namespace M
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.A.M (Frame)
end M
end A
namespace T
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.T.F (BaseValue)
namespace C
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.T.F.C (Value Var)
end C
end F
namespace DR
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.T.DR (completeRSourceRead)
namespace L
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.T.DR.L (Value groups)
end L
end DR
namespace Ret
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.T.Ret (pairedPacking)
end Ret
namespace P
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.T.P (R)
end P
namespace Two
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.T.Two (totalBranches)
end Two
end T
end B
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial)
end R
namespace M
export SourceGeneratedInquiryReceiptAction.Configured.Material (born actual_writeback next_prefix_material)
end M
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme)
end WB

namespace Free
variable {Value Var : Unit → Type} [∀ t,AddCommGroup (Value t)]
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := ()))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))

def write (value : PairValue Value ()) : Env (PairValue Value) cfg.LowVar :=
 fun target _ => by cases target;exact value

theorem written (name : cfg.LowVar ()) :
 (M.born frame cfg (WB.programme frame cfg (write cfg))).activeEnvironment () name =
 (R.actualMaterial frame cfg).raw.eval
  ((R.actualMaterial frame cfg).environment+(R.actualMaterial frame cfg).increment) := by
 have written := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
  (@M.actual_writeback _ _ _ _ _ frame cfg (write cfg))
 have read := congrArg (fun environment : Env (PairValue Value) cfg.LowVar => environment () name) written
 have retained := congrArg (fun material : type_of% (R.actualMaterial frame cfg) =>
  write cfg (material.raw.eval (material.environment+material.increment)) () name)
  (M.next_prefix_material frame cfg (WB.programme frame cfg (write cfg)))
 exact read.trans retained
end Free

local instance baseGroups (n : Nat) : ∀ t,AddCommGroup (B.T.F.BaseValue n t) := B.T.DR.L.groups (PairValue B.T.F.C.Value) n
local instance originGroups (n : Nat) : ∀ t,AddCommGroup (B.T.DR.L.Value (B.T.F.BaseValue n) 2 t) := B.T.DR.L.groups (B.T.F.BaseValue n) 2
local instance runtimeGroups (n : Nat) : ∀ t,AddCommGroup
 (B.T.DR.L.Value (B.T.DR.L.Value (B.T.F.BaseValue n) 2) 0 t) := B.T.DR.L.groups (B.T.DR.L.Value (B.T.F.BaseValue n) 2) 0
local instance valueGroups (n : Nat) : ∀ t,AddCommGroup (B.FC.Value n t) := B.T.DR.L.groups (B.T.F.BaseValue n) 5
local instance valueAddZeroClass (n : Nat) (t : Unit) : AddZeroClass (B.FC.Value n t) :=
 (valueGroups n t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (n : Nat) (t : Unit) : AddZero (B.FC.Value n t) := (valueAddZeroClass n t).toAddZero
local instance nextGroups (n : Nat) : ∀ t,AddCommGroup (PairValue (B.FC.Value n) t) := B.T.DR.L.groups (B.T.F.BaseValue n) 6
local instance nextAddZeroClass (n : Nat) (t : Unit) : AddZeroClass (PairValue (B.FC.Value n) t) :=
 (nextGroups n t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance nextAddZero (n : Nat) (t : Unit) : AddZero (PairValue (B.FC.Value n) t) := (nextAddZeroClass n t).toAddZero

variable (initial : Nat)
variable (frame : B.A.M.Frame (Value := PairValue (B.T.F.BaseValue initial)) (Var := B.T.F.C.Var) (sort := ()))
variable (base : B.A.Programme (PhysicalValue := PairValue (B.T.F.BaseValue initial)) (PhysicalVar := B.T.F.C.Var) (sort := ()))
variable (before : Inventory (V := B.T.F.BaseValue initial) (X := B.T.F.C.Var) (s := ()))
variable (oldEnvironment : Env (B.T.F.BaseValue initial) B.T.F.C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (ActualNativeRelationTransport.AS.stockScalar frame base)))
variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (sourceFrame : B.A.M.Frame (Value := PairValue (PairValue (B.T.F.BaseValue initial))) (Var := B.T.F.C.Var) (sort := ()))
variable (receiver : B.A.M.Frame (Value := B.FC.Value initial) (Var := B.T.F.C.Var) (sort := ()))
local notation "cfg" => B.programme initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame

def writtenValue := (B.nativeBorn initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver).activeEnvironment () ()

theorem written_raw_value :
 writtenValue initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver =
 (R.actualMaterial receiver cfg).raw.eval
  ((R.actualMaterial receiver cfg).environment+(R.actualMaterial receiver cfg).increment) :=
 Free.written receiver cfg ()

theorem written_full_value :
 writtenValue initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver =
 (SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.code initial frame base before oldEnvironment admissions observation nontrivial half).eval
  (SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.codeEnvironment initial frame base before oldEnvironment admissions) :=
 (written_raw_value initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver).trans
  (congrArg₂ (fun expression environment => expression.eval environment)
   (B.material_raw initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)
   (B.material_updated initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver))

theorem written_physical_action :
 B.T.DR.completeRSourceRead initial 2 0
  (writtenValue initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver).1.1.1 =
 B.T.Ret.pairedPacking (B.T.P.R observation nontrivial half (B.T.Two.totalBranches
  (B.T.DR.completeRSourceRead initial 2 0
   (((SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Origin.origin initial frame base before oldEnvironment admissions).native.raw.eval
     (SourceInventoryExecutionFeed.SourceWordNative.afterEnvironment frame base),0),0)))) :=
 (congrArg (fun value : PairValue (B.FC.Value initial) () => B.T.DR.completeRSourceRead initial 2 0 value.1.1.1)
  (written_full_value initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)).trans
  (B.physical_action initial frame base before oldEnvironment admissions observation nontrivial half)

theorem actual_written_physical_action : type_of% (written_physical_action initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
 (B.actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame)) :=
 written_physical_action initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
 (B.actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame)

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
