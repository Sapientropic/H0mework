import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Origin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.FullRSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceInventoryExecutionFeed
namespace O
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Origin (origin sourceRaw sourceUpdated sourceCode sourceEnvironment original_source_action)
end O
namespace T
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action (code)
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
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource
 (born programme lowBase nativeBorn)
namespace Assembly
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource.Assembly
 (programme OldInstallationType oldInstalled SourceInstallationType sourceInstalled reader_preserved decoder_preserved dependent_decoder_preserved)
end Assembly
end F
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode (Value)
end FC
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base root visit actualOccurrence next)
end S
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end I
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current)
end J
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt actual_calculation_state afterEnvironment)
end R
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme oldPaid old_paid_const)
end WB
namespace M
export SourceGeneratedInquiryReceiptAction.Configured.Material
 (programme actual_writeback next_prefix_material material generatedAction nextMaterialFace born whole_first target_next compiles actual_receipt_next native_effect native_inverse)
end M
namespace PT
export SourceGeneratedInquiryReceiptAction.Configured.PairTransport
 (bornPairInventory born_pair_inventory bornSegment)
end PT
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve liftEvent)
end Stock
namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice (originFace)
end SP
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative (afterEnvironment)
end SN
namespace AS
export ActualNativeRelationTransport.AS (stockScalar)
end AS

local instance baseGroups (n : Nat) : ∀ t,AddCommGroup (T.F.BaseValue n t) := T.DR.L.groups (PairValue T.F.C.Value) n
local instance originGroups (n : Nat) : ∀ t,AddCommGroup (T.DR.L.Value (T.F.BaseValue n) 2 t) := T.DR.L.groups (T.F.BaseValue n) 2
local instance runtimeGroups (n : Nat) : ∀ t,AddCommGroup
 (T.DR.L.Value (T.DR.L.Value (T.F.BaseValue n) 2) 0 t) := T.DR.L.groups (T.DR.L.Value (T.F.BaseValue n) 2) 0
local instance actionGroups (n : Nat) : ∀ t,AddCommGroup (PairValue (PairValue (PairValue (T.F.BaseValue n))) t) := T.DR.L.groups (T.F.BaseValue n) 3
local instance valueGroups (n : Nat) : ∀ t,AddCommGroup (FC.Value n t) := T.DR.L.groups (T.F.BaseValue n) 5
local instance valueAddZeroClass (n : Nat) (t : Unit) : AddZeroClass (FC.Value n t) :=
 (valueGroups n t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (n : Nat) (t : Unit) : AddZero (FC.Value n t) := (valueAddZeroClass n t).toAddZero
local instance nextGroups (n : Nat) : ∀ t,AddCommGroup (PairValue (FC.Value n) t) := T.DR.L.groups (T.F.BaseValue n) 6
local instance nextAddZeroClass (n : Nat) (t : Unit) : AddZeroClass (PairValue (FC.Value n) t) :=
 (nextGroups n t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance nextAddZero (n : Nat) (t : Unit) : AddZero (PairValue (FC.Value n) t) := (nextAddZeroClass n t).toAddZero
local instance carryGroups (n : Nat) : ∀ t,AddCommGroup (PairValue (PairValue (FC.Value n)) t) := T.DR.L.groups (T.F.BaseValue n) 7

variable (initial : Nat)
variable (frame : A.M.Frame (Value := PairValue (T.F.BaseValue initial)) (Var := T.F.C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (T.F.BaseValue initial)) (PhysicalVar := T.F.C.Var) (sort := ()))
variable (before : Inventory (V := T.F.BaseValue initial) (X := T.F.C.Var) (s := ()))
variable (oldEnvironment : Env (T.F.BaseValue initial) T.F.C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (AS.stockScalar frame base)))
variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

variable (sourceFrame : A.M.Frame (Value := PairValue (PairValue (T.F.BaseValue initial))) (Var := T.F.C.Var) (sort := ()))
abbrev oldConfiguration := M.programme
 (F.born observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (F.programme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (F.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
local notation "oldCfg" => oldConfiguration initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
variable (receiver : A.M.Frame (Value := FC.Value initial) (Var := T.F.C.Var) (sort := ()))
variable {current : J.Current receiver.registered}
variable (supplied : I.Occurrence receiver (current := current))

structure SourceAt where
 origin : type_of% (SP.originFace frame base before oldEnvironment admissions).rootRead
 currentMaterial : type_of% (I.materialAt receiver supplied)

def sourceAt : SourceAt initial frame base before oldEnvironment admissions receiver supplied :=
 ⟨(SP.originFace frame base before oldEnvironment admissions).rootRead,I.materialAt receiver supplied⟩

def sourceLaw : SourceNativeProjectionLaw (S.base receiver).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit
 ActiveAt := fun _ {_current} _ => PUnit
 InactiveAt := fun _ {_current} _ => PEmpty
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} occurrence _ => SourceAt initial frame base before oldEnvironment admissions receiver occurrence
 project := fun _ {_current} occurrence _ => sourceAt initial frame base before oldEnvironment admissions receiver occurrence

def code : Expr (PairValue (FC.Value initial)) T.F.C.Var () :=
 liftExpr (liftExpr (liftExpr (O.sourceCode initial frame base before oldEnvironment admissions observation nontrivial half)))

def codeEnvironment : Env (PairValue (FC.Value initial)) T.F.C.Var :=
 pairEnvironment (pairEnvironment (pairEnvironment
  (O.sourceEnvironment initial frame base before oldEnvironment admissions) 0) 0) 0

/-- Source input is read from the original material carried by this dependent coface. -/
def codeReader : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (FC.Value initial)) (Var := T.F.C.Var) (sort := ()) :=
 let source := sourceAt initial frame base before oldEnvironment admissions receiver supplied
 let material := source.origin.source.native
 let raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (PairValue (T.F.BaseValue initial))) (Var := T.F.C.Var) (sort := ()) :=
  ⟨pairEnvironment material.environment 0,liftExpr material.raw⟩
 let updated := pairEnvironment (material.environment+material.increment) 0
 let environment := pairEnvironment raw.environment (updated-raw.environment)
 ⟨pairEnvironment (pairEnvironment (pairEnvironment environment 0) 0) 0,
  liftExpr (liftExpr (liftExpr (T.code observation nontrivial half initial raw)))⟩

theorem code_reader_raw :
 (codeReader initial frame base before oldEnvironment admissions observation nontrivial half receiver supplied).expression =
 code initial frame base before oldEnvironment admissions observation nontrivial half := rfl

theorem code_reader_environment :
 (codeReader initial frame base before oldEnvironment admissions observation nontrivial half receiver supplied).environment =
 codeEnvironment initial frame base before oldEnvironment admissions := rfl

def carryAt : Option (Inventory (V := PairValue (PairValue (FC.Value initial))) (X := T.F.C.Var) (s := ())) :=
 let inherited := ((oldCfg).datum receiver).nextPairInventoryAt.bind (fun read => read supplied)
 match receiver.pairInventory with
 | none => inherited
 | some carried => some (Stock.preserve inherited (carried.map Stock.liftEvent))

local notation "Law" => (fun receiver => sourceLaw initial frame base before oldEnvironment admissions receiver)
local notation "Reader" => (fun receiver {_current} supplied => codeReader initial frame base before oldEnvironment admissions observation nontrivial half receiver supplied)
local notation "Carry" => (fun receiver {_current} supplied => carryAt initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver supplied)

def programme : A.Programme (PhysicalValue := FC.Value initial) (PhysicalVar := T.F.C.Var) (sort := ()) :=
 F.Assembly.programme oldCfg Law Reader Carry
local notation "cfg" => programme initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame

def oldInstallation : F.Assembly.OldInstallationType oldCfg Law Reader Carry receiver :=
 F.Assembly.oldInstalled oldCfg Law Reader Carry receiver

def sourceInstallation : F.Assembly.SourceInstallationType oldCfg Law Reader Carry receiver :=
 F.Assembly.sourceInstalled oldCfg Law Reader Carry receiver

def sourceFace : SourceNativeRootSemanticFaceAt (S.root receiver cfg) (S.visit receiver cfg) where
 projection := (sourceInstallation initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

theorem reader_preserved : ((cfg).datum receiver).reader supplied = ((oldCfg).datum receiver).reader supplied :=
 F.Assembly.reader_preserved oldCfg Law Reader Carry receiver supplied
theorem decoder_preserved : ((cfg).datum receiver).nextEnvironmentRead = ((oldCfg).datum receiver).nextEnvironmentRead :=
 F.Assembly.decoder_preserved oldCfg Law Reader Carry receiver

theorem material_raw : (R.actualMaterial receiver cfg).raw = code initial frame base before oldEnvironment admissions observation nontrivial half :=
 code_reader_raw initial frame base before oldEnvironment admissions observation nontrivial half (A.epoch receiver) (S.actualOccurrence receiver)

theorem material_environment : (R.actualMaterial receiver cfg).environment = codeEnvironment initial frame base before oldEnvironment admissions :=
 code_reader_environment initial frame base before oldEnvironment admissions observation nontrivial half (A.epoch receiver) (S.actualOccurrence receiver)

def fullWrite (value : PairValue (FC.Value initial) ()) : Env (PairValue (FC.Value initial)) T.F.C.Var :=
 fun target _ => by cases target; exact value

abbrev lowBase := WB.programme receiver cfg (fullWrite initial)
abbrev generatedAction := M.generatedAction receiver cfg (lowBase initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)
abbrev nativeBorn := M.born receiver cfg (lowBase initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)
abbrev nextMaterialFace := M.nextMaterialFace receiver cfg (lowBase initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)

theorem material_updated :
 (R.actualMaterial receiver cfg).environment+(R.actualMaterial receiver cfg).increment =
 codeEnvironment initial frame base before oldEnvironment admissions := by
 change (R.actualMaterial receiver cfg).environment+
  (R.afterEnvironment receiver cfg-(R.actualMaterial receiver cfg).environment) = _
 apply (add_sub_cancel _ _).trans
 exact code_reader_environment initial frame base before oldEnvironment admissions observation nontrivial half
  (A.epoch (S.next receiver cfg)) (S.actualOccurrence (S.next receiver cfg))

theorem lifted_read :
 (code initial frame base before oldEnvironment admissions observation nontrivial half).eval
  (codeEnvironment initial frame base before oldEnvironment admissions) =
 ((((O.sourceCode initial frame base before oldEnvironment admissions observation nontrivial half).eval
   (O.sourceEnvironment initial frame base before oldEnvironment admissions),0),0),0) := by
 unfold code codeEnvironment
 rw [eval_liftExpr,Expr.effect_zero,eval_liftExpr,Expr.effect_zero,eval_liftExpr,Expr.effect_zero]

theorem physical_action :
 T.DR.completeRSourceRead initial 2 0
  (((code initial frame base before oldEnvironment admissions observation nontrivial half).eval
   (codeEnvironment initial frame base before oldEnvironment admissions)).1.1.1) =
 T.Ret.pairedPacking (T.P.R observation nontrivial half (T.Two.totalBranches
  (T.DR.completeRSourceRead initial 2 0
   (((O.origin initial frame base before oldEnvironment admissions).native.raw.eval
     (SN.afterEnvironment frame base),0),0)))) := by
 rw [lifted_read]
 exact O.original_source_action initial frame base before oldEnvironment admissions observation nontrivial half

abbrev oldPaid := WB.oldPaid receiver cfg

def actualTrace : Trace (R.actualMaterial receiver cfg).environment
 (code initial frame base before oldEnvironment admissions observation nontrivial half)
 (.const (oldPaid initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)) :=
 Eq.mp (congrArg (fun terminal => Trace (R.actualMaterial receiver cfg).environment
  (code initial frame base before oldEnvironment admissions observation nontrivial half) terminal)
  (WB.old_paid_const receiver cfg))
  (Eq.mp (congrArg (fun expression => Trace (R.actualMaterial receiver cfg).environment expression
    (R.actualMaterial receiver cfg).state.1)
   (material_raw initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver))
   (R.actualMaterial receiver cfg).state.2)

abbrev pairInventory := PT.bornPairInventory receiver cfg (fullWrite initial)
theorem born_pair_inventory : type_of% (PT.born_pair_inventory receiver cfg (fullWrite initial)) :=
 PT.born_pair_inventory receiver cfg (fullWrite initial)

theorem whole_first : type_of% (M.whole_first receiver cfg
 (lowBase initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)) :=
 M.whole_first receiver cfg (lowBase initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)

theorem target_next : type_of% (M.target_next receiver cfg
 (lowBase initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)) :=
 M.target_next receiver cfg (lowBase initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver)

/-- This target is the actual FullR birth with its matching original continuation. -/
abbrev actualCurrent := F.nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

def actualBorn := nativeBorn initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
 (actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame)

theorem actual_whole_first : type_of% (whole_first initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
 (actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame)) :=
 whole_first initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
 (actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame)

theorem actual_target_next : type_of% (target_next initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
 (actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame)) :=
 target_next initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
 (actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame)

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
