import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Model.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation CofinalHistorySettlement
open private native_acted_read from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Model.Consumer
namespace Feed
export SourceInventoryExecutionFeed (Inventory written)
end Feed
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace AR
export SourceInventoryExecutionFeed.AdmissionReceipt (Admission)
end AR
namespace FG
export SourceInventoryExecutionFeed.FeedGeneratorOccurrence (fromRelationItem fromRelationItem_expression)
end FG
namespace SG
export ActualNativeRelationTransport.SourceGeneratorAdmission (generator generator_expression sourceExpression)
end SG
namespace SA
export ActualCofinalSourceAction (selected nativePacket sourceWordAction sourceBorn environmentTransport wordTransport)
end SA
namespace Steps
export ActualNativeRelationTransport (paid_step_source_occurrence born_stock bornStock decoded_environment)
end Steps
namespace Engine
export ActualNativeRelationTransport.AS (stockScalar stockDecodedEnvironment stockCfg)
end Engine
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
 (request nextOriginFace nextFullValue sourceWord actual_updated_value whole_first canonical_next answered_next)
end SN
namespace W
export NativeSigma.Writeback (receiptSelected nativeTrace nativeBoundary bornWord admissionValue)
end W
local instance wordNativeGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

def inventoryTransport {V Y Z : Unit → Type} [∀ target,AddCommGroup (V target)]
 (same : Y = Z) : Feed.Inventory (V := V) (X := Y) (s := ()) → Feed.Inventory (V := V) (X := Z) (s := ()) := by
 cases same
 exact id

def relationTransport {V Y Z : Unit → Type} [∀ target,AddCommGroup (V target)]
 (same : Y = Z) {source : Feed.Inventory (V := V) (X := Y) (s := ())}
 (occurrence : WR.RelationOccurrence source) : WR.RelationOccurrence (inventoryTransport same source) := by
 cases same
 exact occurrence

theorem lift_word_transport {V Y Z : Unit → Type} [∀ target,AddCommGroup (V target)]
 (same : Y = Z) (word : Formal ℤ V Y ()) :
 liftMap (R := ℤ) (SA.wordTransport same word) = SA.wordTransport same (liftMap (R := ℤ) word) := by
 cases same
 rfl

/-- The source item selects its own old Feed execution and its literal admitted generator. -/
def packetAdmission (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
 (source : Feed.Inventory (V := L.Value (PairValue C.Value) packet.1) (X := C.Var) (s := ()))
 (environment : Env (L.Value (PairValue C.Value) packet.1) C.Var)
 (present : packet.2.1.1.inventory = some (Feed.written environment source))
 (occurrence : WR.RelationOccurrence source) :
 AR.Admission (inventoryTransport packet.2.2.2.down.symm source)
  (Engine.stockScalar (SA.selected factory packet) (SA.nativePacket factory packet).2.2.1) := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  let packet : NativeSigma.NativePacket := ⟨grade,data,⟨C.Var,datum,inventory,pairInventory⟩,⟨rfl⟩⟩
  refine ⟨occurrence,?_⟩
  intro item
  let generated := FG.fromRelationItem environment source occurrence item
  refine ⟨SG.generator factory packet (Feed.written environment source) present generated,?_⟩
  exact (SG.generator_expression factory packet _ present generated).trans
    (congrArg (SG.sourceExpression packet) (FG.fromRelationItem_expression environment source occurrence item))

theorem packet_admission_word (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
 (source : Feed.Inventory (V := L.Value (PairValue C.Value) packet.1) (X := C.Var) (s := ()))
 (environment : Env (L.Value (PairValue C.Value) packet.1) C.Var)
 (present : packet.2.1.1.inventory = some (Feed.written environment source))
 (occurrence : WR.RelationOccurrence source) :
 (packetAdmission factory packet source environment present occurrence).1.word =
  SA.wordTransport packet.2.2.2.down.symm occurrence.word := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  rfl

def oldStock (native : NativeSigma.NativePacket) := Engine.stockScalar (W.receiptSelected native) native.2.2.1
def oldEnvironment (native : NativeSigma.NativePacket) := Engine.stockDecodedEnvironment (W.receiptSelected native) native.2.2.1

private theorem born_inventory (native : NativeSigma.NativePacket) :
 (AS.bornAfterNative native).2.1.1.inventory = some (Feed.written (oldEnvironment native) (oldStock native)) := by
 simpa only [AS.bornAfterNative,AS.localNativeReceipt,W.receiptSelected,oldEnvironment,oldStock,Steps.bornStock] using
  Steps.born_stock (W.receiptSelected native) native.2.2.1

abbrev originalOccurrence (native : NativeSigma.NativePacket)
 (index : Fin (W.nativeTrace native |> SourceOperationPaidRelations.words).length) :=
 Steps.paid_step_source_occurrence (W.receiptSelected native) native.2.2.1 index

def beforeStock (native : NativeSigma.NativePacket) :=
 inventoryTransport (AS.bornAfterNative native).2.2.2.down.symm (oldStock native)
def beforeEnvironment (native : NativeSigma.NativePacket) :=
 SA.environmentTransport (AS.bornAfterNative native).2.2.2.down.symm (oldEnvironment native)
abbrev sourceFrame (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 SA.selected factory (AS.bornAfterNative native)
abbrev sourceBase (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 (SA.nativePacket factory (AS.bornAfterNative native)).2.2.1

def admissions (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 List (AR.Admission (beforeStock native) (Engine.stockScalar (sourceFrame factory native) (sourceBase factory native))) :=
 List.ofFn fun index => packetAdmission factory (AS.bornAfterNative native) (oldStock native)
  (oldEnvironment native) (born_inventory native) (originalOccurrence native index)

def request (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 SN.request (V := L.Value (PairValue C.Value) (AS.bornAfterNative native).1)
  (sourceFrame factory native) (sourceBase factory native) (beforeStock native) (beforeEnvironment native)
  (admissions factory native)
def nextFace (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 SN.nextOriginFace (V := L.Value (PairValue C.Value) (AS.bornAfterNative native).1)
  (sourceFrame factory native) (sourceBase factory native) (beforeStock native) (beforeEnvironment native)
  (admissions factory native)
def fullValue (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 W.admissionValue factory (AS.bornAfterNative native)
 (SN.nextFullValue (V := L.Value (PairValue C.Value) (AS.bornAfterNative native).1)
  (sourceFrame factory native) (sourceBase factory native) (beforeStock native) (beforeEnvironment native)
  (admissions factory native))

theorem admissions_words (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 (admissions factory native).map (fun admission => admission.1.word) =
  (SourceOperationPaidRelations.words (W.nativeTrace native)).map
   (SA.wordTransport (AS.bornAfterNative native).2.2.2.down.symm) := by
 unfold admissions
 rw [List.map_ofFn]
 have indexed : (List.ofFn fun index =>
   (originalOccurrence native index).word) = SourceOperationPaidRelations.words (W.nativeTrace native) :=
  List.ofFn_get _
 have transformed := congrArg (List.map (SA.wordTransport (AS.bornAfterNative native).2.2.2.down.symm)) indexed
 rw [List.map_ofFn] at transformed
 apply (congrArg List.ofFn ?_).trans transformed
 funext index
 exact packet_admission_word factory (AS.bornAfterNative native) (oldStock native)
  (oldEnvironment native) (born_inventory native) (originalOccurrence native index)

theorem source_word (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 SN.sourceWord (V := L.Value (PairValue C.Value) (AS.bornAfterNative native).1)
   (sourceFrame factory native) (sourceBase factory native) (beforeStock native) (admissions factory native) =
  SA.sourceWordAction (AS.bornAfterNative native) (W.bornWord native (W.nativeBoundary native)) := by
 change liftMap (R := ℤ) ((admissions factory native).map (fun admission => admission.1.word)).sum = _
 rw [admissions_words, ← map_list_sum, SourceOperationPaidRelations.paid_boundary]
 change liftMap (R := ℤ)
   (SA.wordTransport (AS.bornAfterNative native).2.2.2.down.symm (W.nativeBoundary native)) =
  SA.wordTransport (AS.bornAfterNative native).2.2.2.down.symm (liftMap (R := ℤ) (W.nativeBoundary native))
 exact lift_word_transport _ _

theorem full_value (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 fullValue factory native = Recurrence.actualUpdatedValue factory native := by
 have generated := SourceInventoryExecutionFeed.SourceWordNative.next_full_value
  (V := L.Value (PairValue C.Value) (AS.bornAfterNative native).1)
  (sourceFrame factory native) (sourceBase factory native) (beforeStock native) (beforeEnvironment native)
  (admissions factory native)
 rw [source_word] at generated
 have environment : Engine.stockDecodedEnvironment (sourceFrame factory native) (sourceBase factory native) =
   (SA.sourceBorn factory (AS.bornAfterNative native)).2.1.1.activeEnvironment :=
  (Steps.decoded_environment (sourceFrame factory native) (sourceBase factory native)).symm
 have cast_heq : ∀ {α β : Type} (same : α = β) (value : α), HEq (Eq.mp same value) value := by
  intro α β same value
  cases same
  rfl
 have read : W.admissionValue factory (AS.bornAfterNative native)
   (evaluation (R := ℤ) (SA.sourceBorn factory (AS.bornAfterNative native)).2.1.1.activeEnvironment
    (SA.sourceWordAction (AS.bornAfterNative native) (W.bornWord native (W.nativeBoundary native)))) =
   Recurrence.actualUpdatedValue factory native :=
  eq_of_heq ((cast_heq _ _).trans
   (native_acted_read factory (AS.bornAfterNative native) (W.bornWord native (W.nativeBoundary native))))
 exact (congrArg (W.admissionValue factory (AS.bornAfterNative native))
  (generated.trans (congrArg (fun environment => evaluation (R := ℤ) environment
   (SA.sourceWordAction (AS.bornAfterNative native) (W.bornWord native (W.nativeBoundary native)))) environment))).trans read

attribute [local irreducible] AS.localNativeReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
abbrev native := originalNative observation nontrivial half depth (ordinal+1)
def originalRequest := request (D.factory observation nontrivial half) (native observation nontrivial half depth ordinal)
def originalNextFace := nextFace (D.factory observation nontrivial half) (native observation nontrivial half depth ordinal)
def originalFullValue := fullValue (D.factory observation nontrivial half) (native observation nontrivial half depth ordinal)

theorem original_full_value : originalFullValue observation nontrivial half depth ordinal =
 Recurrence.actualUpdatedValue (D.factory observation nontrivial half) (native observation nontrivial half depth ordinal) :=
 full_value _ _

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
