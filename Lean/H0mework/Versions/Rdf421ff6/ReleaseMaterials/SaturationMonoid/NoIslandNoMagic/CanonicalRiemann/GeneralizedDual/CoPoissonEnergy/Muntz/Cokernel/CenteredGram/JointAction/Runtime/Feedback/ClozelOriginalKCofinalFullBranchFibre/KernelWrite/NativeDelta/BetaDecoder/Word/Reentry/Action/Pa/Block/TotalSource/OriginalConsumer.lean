import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.OriginalFullRConsumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace B
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
 (actualBorn actualCurrent actual_whole_first actual_target_next sourceFace sourceInstallation programme actualTrace born_pair_inventory)
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Consumer
 (writtenValue actual_written_physical_action)
end B
namespace O
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Origin (origin)
end O
namespace Physics
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.Ret (pairedPacking)
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.P (R)
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.Two (totalBranches)
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.DR (completeRSourceRead)
end Physics
namespace N
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction (BaseValue)
end N
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode (Value)
end FC
namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice (born)
end SP
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative (afterEnvironment nextFullValue next_full_value)
end SN

local instance baseGroups (initial : Nat) : ∀ t,AddCommGroup (N.BaseValue initial t) := L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t,AddCommGroup (L.Value (N.BaseValue initial) 2 t) := L.groups (N.BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ t,AddCommGroup
 (L.Value (L.Value (N.BaseValue initial) 2) 0 t) := L.groups (L.Value (N.BaseValue initial) 2) 0
local instance valueGroups (initial : Nat) : ∀ t,AddCommGroup (FC.Value initial t) := L.groups (N.BaseValue initial) 5
local instance valueAddZeroClass (initial : Nat) (t : Unit) : AddZeroClass (FC.Value initial t) :=
 (valueGroups initial t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (initial : Nat) (t : Unit) : AddZero (FC.Value initial t) := (valueAddZeroClass initial t).toAddZero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
section ReadAt
variable (initial : Nat)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := PairValue (N.BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := PairValue (N.BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : SourceInventoryExecutionFeed.Inventory (V := N.BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (N.BaseValue initial) C.Var)
variable (admissions : List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission before
 (ActualNativeRelationTransport.AS.stockScalar frame base)))

/-- The actual admitted trace, not a query equality, identifies the full original word update. -/
theorem origin_full_value :
 (O.origin initial frame base before oldEnvironment admissions).native.raw.eval (SN.afterEnvironment frame base) =
 SN.nextFullValue frame base before oldEnvironment admissions :=
 (O.origin initial frame base before oldEnvironment admissions).newTrace.sound.trans
  (SN.next_full_value frame base before oldEnvironment admissions).symm

local notation "sf" => SP.born (V := N.BaseValue initial) frame base before oldEnvironment admissions
local notation "actual" => B.actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sf
local notation "cfg" => B.programme initial frame base before oldEnvironment admissions observation nontrivial half sf

theorem actual_source_update :
 Physics.completeRSourceRead initial 2 0
  (B.writtenValue initial frame base before oldEnvironment admissions observation nontrivial half sf actual).1.1.1 =
 Physics.pairedPacking (Physics.R observation nontrivial half (Physics.totalBranches
  (Physics.completeRSourceRead initial 2 0 ((SN.nextFullValue frame base before oldEnvironment admissions,0),0)))) :=
 (B.actual_written_physical_action initial frame base before oldEnvironment admissions observation nontrivial half sf).trans
  (congrArg (fun value : PairValue (N.BaseValue initial) () =>
   Physics.pairedPacking (Physics.R observation nontrivial half (Physics.totalBranches
    (Physics.completeRSourceRead initial 2 0 ((value,0),0)))))
   (origin_full_value initial frame base before oldEnvironment admissions))

private def bundleAt :=
 let source := (B.sourceFace initial frame base before oldEnvironment admissions observation nontrivial half sf actual).rootRead
 let born := B.actualBorn initial frame base before oldEnvironment admissions observation nontrivial half sf
 let trace := B.actualTrace initial frame base before oldEnvironment admissions observation nontrivial half sf actual
 let actualData := (source,born,trace)
 let physical := actual_source_update observation nontrivial half initial frame base before oldEnvironment admissions
 PProd.mk
  (⟨actualData,rfl⟩ : { output : type_of% actualData // output = actualData })
  (And.intro (origin_full_value initial frame base before oldEnvironment admissions) <|
   And.intro physical <|
   And.intro (B.born_pair_inventory initial frame base before oldEnvironment admissions observation nontrivial half sf actual) <|
   And.intro (B.actual_whole_first initial frame base before oldEnvironment admissions observation nontrivial half sf)
    (B.actual_target_next initial frame base before oldEnvironment admissions observation nontrivial half sf))

def ResultAt := type_of% (bundleAt observation nontrivial half initial frame base before oldEnvironment admissions)
def readAt : ResultAt observation nontrivial half initial frame base before oldEnvironment admissions :=
 bundleAt observation nontrivial half initial frame base before oldEnvironment admissions
end ReadAt

attribute [local irreducible] ResultAt
variable (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
private def InputAt (initial : Nat) (varFamily : Unit → Type) :=
 Σ frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PairValue (N.BaseValue initial)) (Var := varFamily) (sort := ()),
 Σ base : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := PairValue (N.BaseValue initial)) (PhysicalVar := varFamily) (sort := ()),
 Σ before : SourceInventoryExecutionFeed.Inventory (V := N.BaseValue initial) (X := varFamily) (s := ()),
 Env (N.BaseValue initial) varFamily ×
 List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission before
  (ActualNativeRelationTransport.AS.stockScalar frame base))

def packetRead :
 (stock : SourceInventoryExecutionFeed.Inventory (V := N.BaseValue packet.1) (X := packet.2.2.1.LowVar) (s := ())) →
 (environment : Env (N.BaseValue packet.1) packet.2.2.1.LowVar) →
 (admissions : List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission stock
  (ActualNativeRelationTransport.AS.stockScalar (ActualCofinalSourceAction.selected factory packet)
   (ActualCofinalSourceAction.nativePacket factory packet).2.2.1))) →
 PSigma (fun Result : Type _ => Result) := by
 intro stock environment admissions
 let source : InputAt packet.1 packet.2.2.1.LowVar :=
  ⟨ActualCofinalSourceAction.selected factory packet,
   (ActualCofinalSourceAction.nativePacket factory packet).2.2.1,stock,environment,admissions⟩
 let target : InputAt packet.1 C.Var :=
  Eq.mp (congrArg (InputAt packet.1) packet.2.2.2.down) source
 let output := readAt observation nontrivial half packet.1 target.1 target.2.1 target.2.2.1 target.2.2.2.1 target.2.2.2.2
 exact ⟨type_of% output,output⟩

attribute [local irreducible] AS.localNativeReceipt
variable (depth ordinal : Nat)
local notation "native" => originalNative observation nontrivial half depth (ordinal+1)
local notation "factory₀" => D.factory observation nontrivial half

def originalRead := packetRead observation nontrivial half factory₀ (AS.bornAfterNative native)
 (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory₀ native)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
