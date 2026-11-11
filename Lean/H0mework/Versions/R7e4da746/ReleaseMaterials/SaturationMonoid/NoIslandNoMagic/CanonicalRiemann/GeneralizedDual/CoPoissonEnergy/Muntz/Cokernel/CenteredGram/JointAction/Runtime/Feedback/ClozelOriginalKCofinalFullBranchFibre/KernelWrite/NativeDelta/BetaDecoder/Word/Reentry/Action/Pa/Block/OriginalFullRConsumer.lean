import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.FullRConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalFullRConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace N
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction (BaseValue)
end N
namespace Pa
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa (CodeValue)
end Pa
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource
 (inventory born_pair_inventory whole_first target_next actual_receipt_next)
end F
namespace Q
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRConsumer
 (receipts sourceInput writtenValue written_full_value actual_full_action actual_np_unit actual_pn_inverse
  actual_occurrence_positions npWritten pnWritten np_written_word pn_written_word prior_event_written
  actual_pa_physical actual_pa_positionGap actual_pa_response actual_pa_unit_rank)
end Q
namespace Code
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode (Value)
end Code
namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice (born)
end SP

local instance baseGroups (initial : Nat) : ∀ t, AddCommGroup (N.BaseValue initial t) :=
 L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t, AddCommGroup (L.Value (N.BaseValue initial) 2 t) :=
 L.groups (N.BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ t,
 AddCommGroup (L.Value (L.Value (N.BaseValue initial) 2) 0 t) := L.groups (L.Value (N.BaseValue initial) 2) 0

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
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
variable (sourceFrame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := PairValue (PairValue (N.BaseValue initial))) (Var := C.Var) (sort := ()))

local notation "two" => Q.receipts observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "source" => Q.sourceInput observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "written" => Q.writtenValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "npSlot" => Q.npWritten observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "pnSlot" => Q.pnWritten observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

/-- One actual tuple binds the input, write and both literal slots to this complete source. -/
private def bundleAt :=
 let actualData := (source,written,two,npSlot,pnSlot)
 PProd.mk
  (⟨actualData,rfl⟩ : {output : type_of% actualData // output = actualData})
  (And.intro (Q.written_full_value observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_np_unit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_pn_inverse observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_full_action observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_pa_physical observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_pa_positionGap observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_pa_response observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_pa_unit_rank observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.actual_occurrence_positions observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (F.born_pair_inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (F.whole_first observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (F.target_next observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (F.actual_receipt_next observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.np_written_word observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) <|
   And.intro (Q.pn_written_word observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
    (Q.prior_event_written observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))

def ResultAt := type_of% (bundleAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def readAt : ResultAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame :=
 bundleAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

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

/-- Transport the complete dependent input along the packet's full variable-family equality. -/
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
 let frame := target.1
 let base := target.2.1
 let before := target.2.2.1
 let oldEnvironment := target.2.2.2.1
 let actualAdmissions := target.2.2.2.2
 let output := readAt observation nontrivial half packet.1 frame base before oldEnvironment actualAdmissions
  (SP.born (V := N.BaseValue packet.1) frame base before oldEnvironment actualAdmissions)
 exact ⟨type_of% output, output⟩

variable (stock : SourceInventoryExecutionFeed.Inventory (V := N.BaseValue packet.1) (X := packet.2.2.1.LowVar) (s := ()))
variable (environment : Env (N.BaseValue packet.1) packet.2.2.1.LowVar)
variable (admissions : List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission stock
 (ActualNativeRelationTransport.AS.stockScalar (ActualCofinalSourceAction.selected factory packet)
  (ActualCofinalSourceAction.nativePacket factory packet).2.2.1)))

abbrev PacketRead := (packetRead observation nontrivial half factory packet stock environment admissions).1

attribute [local irreducible] AS.localNativeReceipt
variable (depth ordinal : Nat)
local notation "native" => originalNative observation nontrivial half depth (ordinal+1)
local notation "factory₀" => D.factory observation nontrivial half

theorem original_consumed : Nonempty (PacketRead observation nontrivial half factory₀
 (AS.bornAfterNative native) (WordNative.beforeStock native) (WordNative.beforeEnvironment native)
 (WordNative.admissions factory₀ native)) :=
 ⟨(packetRead observation nontrivial half factory₀ (AS.bornAfterNative native)
   (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory₀ native)).2⟩

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalFullRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
