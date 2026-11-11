import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.OriginalConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalRAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open BurnolPhysicalState
namespace B
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
 (actualBorn actualCurrent actual_whole_first actual_target_next programme)
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Consumer
 (writtenValue)
end B
namespace Physics
export OriginalTotalSourceConsumer.Physics (completeRSourceRead pairedPacking R totalBranches)
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
export SourceInventoryExecutionFeed.SourceWordNative (nextFullValue)
end SN
namespace DR
export OriginalKSourceDifferentialResidualAction (sourceCollapseHom source_collapse_actual completeRSourceRead)
end DR
namespace W
export NativeSigma.Writeback (admissionValue)
end W
local instance baseGroups (initial : Nat) : ∀ t,AddCommGroup (N.BaseValue initial t) := L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t,AddCommGroup (L.Value (N.BaseValue initial) 2 t) := L.groups (N.BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ t,AddCommGroup
 (L.Value (L.Value (N.BaseValue initial) 2) 0 t) := L.groups (L.Value (N.BaseValue initial) 2) 0
local instance valueGroups (initial : Nat) : ∀ t,AddCommGroup (FC.Value initial t) := L.groups (N.BaseValue initial) 5
local instance valueAddZeroClass (initial : Nat) (t : Unit) : AddZeroClass (FC.Value initial t) :=
 (valueGroups initial t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (initial : Nat) (t : Unit) : AddZero (FC.Value initial t) := (valueAddZeroClass initial t).toAddZero

private theorem cast_roundtrip {α β : Type} (same : α=β) (value : α) :
 Eq.mp same.symm (Eq.mp same value)=value := by cases same; rfl

theorem read_admission (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
 (value : PairValue (N.BaseValue packet.1) ()) :
 Physics.completeRSourceRead packet.1 2 0 ((value,0),0) =
 NativeSigma.collapseNative factory packet (W.admissionValue factory packet value) := by
 unfold NativeSigma.collapseNative W.admissionValue
 rw [cast_roundtrip]
 change DR.sourceCollapseHom packet.1 ((value+0)+(0+0)) = _
 rw [add_zero,zero_add,DR.source_collapse_actual,add_zero]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
section At
variable (initial : Nat)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := PairValue (N.BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := PairValue (N.BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : SourceInventoryExecutionFeed.Inventory (V := N.BaseValue initial) (X := C.Var) (s := ()))
variable (environment : Env (N.BaseValue initial) C.Var)
variable (admissions : List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission before
 (ActualNativeRelationTransport.AS.stockScalar frame base)))
local notation "sf" => SP.born (V := N.BaseValue initial) frame base before environment admissions
local notation "current" => B.actualCurrent initial frame base before environment admissions observation nontrivial half sf

private theorem equationAt : type_of%
 (congrArg (fun value : PairValue (PairValue C.Value) () => value.1.1)
  (OriginalTotalSourceConsumer.actual_source_update observation nontrivial half initial frame base before environment admissions)) :=
 congrArg (fun value : PairValue (PairValue C.Value) () => value.1.1)
  (OriginalTotalSourceConsumer.actual_source_update observation nontrivial half initial frame base before environment admissions)

private def equationLeft {α : Type} {left right : α} (_proof : left=right) := left

def pointAt : BurnolL2 := equationLeft
 (equationAt observation nontrivial half initial frame base before environment admissions)

theorem actionAt :
 pointAt observation nontrivial half initial frame base before environment admissions =
 Physics.R observation nontrivial half (Physics.totalBranches
  (Physics.completeRSourceRead initial 2 0 ((SN.nextFullValue frame base before environment admissions,0),0))) :=
 equationAt observation nontrivial half initial frame base before environment admissions

end At

attribute [local irreducible] pointAt

private def InputAt (initial : Nat) (varFamily : Unit → Type) :=
 Σ frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PairValue (N.BaseValue initial)) (Var := varFamily) (sort := ()),
 Σ base : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := PairValue (N.BaseValue initial)) (PhysicalVar := varFamily) (sort := ()),
 Σ before : SourceInventoryExecutionFeed.Inventory (V := N.BaseValue initial) (X := varFamily) (s := ()),
 Env (N.BaseValue initial) varFamily ×
 List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission before
  (ActualNativeRelationTransport.AS.stockScalar frame base))

private def sourceValue (initial : Nat) {varFamily : Unit → Type} (source : InputAt initial varFamily) :=
 SN.nextFullValue source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2

private theorem sourceValue_transport (initial : Nat) {Y Z : Unit → Type}
 (same : Y=Z) (source : InputAt initial Y) :
 sourceValue initial (Eq.mp (congrArg (InputAt initial) same) source) = sourceValue initial source := by
 cases same
 rfl


/-- Keep the actual point with its equation to avoid a duplicate runtime header. -/
private def sourceEquation (initial : Nat) {varFamily : Unit → Type}
 (same : varFamily=C.Var) (source : InputAt initial varFamily) :=
 let target : InputAt initial C.Var := Eq.mp (congrArg (InputAt initial) same) source
 let actual := (actionAt observation nontrivial half initial
  target.1 target.2.1 target.2.2.1 target.2.2.2.1 target.2.2.2.2).trans
  (congrArg (fun value : PairValue (N.BaseValue initial) () =>
   Physics.R observation nontrivial half
    (Physics.totalBranches (Physics.completeRSourceRead initial 2 0 ((value,0),0))))
   (sourceValue_transport initial same source))
 PProd.mk (equationLeft actual) actual


section Packet
variable (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
variable (stock : SourceInventoryExecutionFeed.Inventory (V := N.BaseValue packet.1) (X := packet.2.2.1.LowVar) (s := ()))
variable (environment : Env (N.BaseValue packet.1) packet.2.2.1.LowVar)
variable (admissions : List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission stock
 (ActualNativeRelationTransport.AS.stockScalar (ActualCofinalSourceAction.selected factory packet)
  (ActualCofinalSourceAction.nativePacket factory packet).2.2.1)))

def packetInput : BurnolL2 := Physics.totalBranches
 (NativeSigma.collapseNative factory packet (W.admissionValue factory packet
  (SN.nextFullValue
   (ActualCofinalSourceAction.selected factory packet)
   (ActualCofinalSourceAction.nativePacket factory packet).2.2.1 stock environment admissions)))

def packetAction :=
 let source : InputAt packet.1 packet.2.2.1.LowVar :=
  ⟨ActualCofinalSourceAction.selected factory packet,
   (ActualCofinalSourceAction.nativePacket factory packet).2.2.1,stock,environment,admissions⟩
 let actual := (sourceEquation observation nontrivial half packet.1 packet.2.2.2.down source).2.trans
  (congrArg (fun value => Physics.R observation nontrivial half (Physics.totalBranches value))
   (read_admission factory packet (sourceValue packet.1 source)))
 PProd.mk (equationLeft actual) actual

def packetPoint : BurnolL2 :=
 (packetAction observation nontrivial half factory packet stock environment admissions).1

attribute [local irreducible] packetPoint packetInput

end Packet

theorem packet_input_word (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 packetInput factory (AS.bornAfterNative native)
  (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory native) =
 Physics.totalBranches (NativeSigma.collapseNative factory (AS.bornAfterNative native)
  (Recurrence.actualUpdatedValue factory native)) :=
 congrArg (fun value => Physics.totalBranches
  (NativeSigma.collapseNative factory (AS.bornAfterNative native) value)) (WordNative.full_value factory native)

attribute [local irreducible] AS.localNativeReceipt L.Value
variable (depth ordinal : Nat)
local notation "native" => originalNative observation nontrivial half depth (ordinal+1)
local notation "factory₀" => D.factory observation nontrivial half

def originalPoint := packetPoint observation nontrivial half factory₀ (AS.bornAfterNative native)
 (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory₀ native)

theorem original_action : originalPoint observation nontrivial half depth ordinal =
 Physics.R observation nontrivial half (Recurrence.physicalUpdated observation nontrivial half depth ordinal) := by
 have actual := (packetAction observation nontrivial half factory₀ (AS.bornAfterNative native)
  (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory₀ native)).2
 exact actual.trans (congrArg (Physics.R observation nontrivial half)
  (packet_input_word factory₀ native))

theorem original_positionGap : originalPoint observation nontrivial half depth ordinal ∈
 locallyConstantFace burnolUnscaledCommonGapRadius := by
 rw [original_action,OriginalKCombCofinalRAction.original_R_direct]
 apply CombSource.Pricing.ambient_R_positionGap (observation.coordinate/2)
  (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)
 rw [Recurrence.original_updated_total]
 exact (locallyConstantFace burnolUnscaledCommonGapRadius).sub_mem
  (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth (ordinal+3))
  (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth (ordinal+1))

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
