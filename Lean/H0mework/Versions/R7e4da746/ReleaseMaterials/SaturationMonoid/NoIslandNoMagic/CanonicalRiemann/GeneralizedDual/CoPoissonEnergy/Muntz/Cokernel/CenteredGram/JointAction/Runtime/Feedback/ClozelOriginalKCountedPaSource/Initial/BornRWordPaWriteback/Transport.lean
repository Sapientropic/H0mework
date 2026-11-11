import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Prefix

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback
open CenteredGram.IntegralGraphJointAction
open private observedTrace datum source compiledOccurrence from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve mapped_trace)
end Stock
namespace Lower
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end Lower
namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (priorSeed updatedSeed)
end IP
namespace Res
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (liftEvent liftedInventory priorPairInventory pairInventory)
end Res
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (completeWrittenInventory complete_written_preserves disposition)
end J
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (seed)
end I
namespace Act
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end Act
private theorem produced_normalized
 {S:Type} {V X:S→Type} [∀t,AddCommGroup (V t)] {s:S}
 {NW:WorldRelationNetwork} {Voc:Vocabulary}
 {old:SourceNativeAuthoritativeRootClosure NW Voc} {origin:Voc.Current}
 {env:Env V X} {operation:V s→+V s} {input:Expr V X s}
 (data:Produced old origin env operation input):
 data.gamma=data.omega-constantMap (R:=ℤ) data.nu:=by
 rw [data.gamma_source,data.omega_source,data.nu_source]
 exact normalized_word old origin env operation input

local instance transportGroups (n:Nat):∀t,AddCommGroup (Lower.Value A.W n t):=BornRCanonicalMethodRuntime.levelGroups n
local instance transportPairGroups (n:Nat):∀t,AddCommGroup (PairValue (Lower.Value A.W n) t):=
 fun t=>@Prod.instAddCommGroup (Lower.Value A.W n t) (Lower.Value A.W n t)
  (BornRCanonicalMethodRuntime.levelGroups n t) (BornRCanonicalMethodRuntime.levelGroups n t)
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "slot"=>CompletedSourceRCalculation.Slot.branches
local notation "factory"=>A.fixedRFactory observation nontrivial half
local notation "initial"=>H.receiver observation nontrivial half depth ordinal
local notation "pR"=>H.methodProgramme observation nontrivial half depth ordinal
attribute [local irreducible] installedMethod

private theorem preserve_generated {X:Type} (prior:Option (RootedAccountedUnfolding X))
 (generated:RootedAccountedUnfolding X) (event:X) (present:event∈generated.trace):
 event∈(Stock.preserve prior generated).trace:=by
 cases prior with
 | none=>exact present
 | some carried=>exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

private theorem preserve_carried {X:Type} (prior generated:RootedAccountedUnfolding X)
 (event:X) (present:event∈prior.trace):event∈(Stock.preserve (some prior) generated).trace:=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem source_in_scalar (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):
 (show Prop from by
  rcases source with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
  cases language
  exact ∀event∈(A.nativeWordInventory observation nontrivial half n frame).trace,
   event∈(AS.scalar factory n ⟨frame,seed⟩ ⟨A.X,datum,scalar,pair⟩ rfl).trace):=by
 rcases source with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
 cases language
 change ∀event∈(A.nativeWordInventory observation nontrivial half n frame).trace,
  event∈(AS.scalar factory n ⟨frame,seed⟩ ⟨A.X,datum,scalar,pair⟩ rfl).trace
 intro event present
 unfold AS.scalar
 apply preserve_generated
 apply preserve_generated
 apply preserve_carried
 have generated:=preserve_generated
  ((BornRCanonicalMethodRuntime.SF.defaultFactory A.W A.X slot).extraScalar n seed frame)
  (A.nativeWordInventory observation nontrivial half n frame) event present
 exact BornRCanonicalMethodRuntime.nativeGammaAction_keeps_prior
  observation nontrivial half n seed frame event generated

-- The appended source query is irrelevant to the old word's dependent normalization.
attribute [local irreducible] BornRCanonicalMethodRuntime.nativeGammaActionData
 BornRCanonicalMethodRuntime.nativeGammaActionInventory BornRCanonicalMethodRuntime.nativeGammaActionScalar

private def selected (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):=
 S.Complete.atReceipt (AS.stockCfg source.2.2.1) source.2.1.1 0

def actualBornHistory (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):=
 AN.bornHistory (selected (AS.nativeAfterAdmission factory source))
  (AS.nativeAfterAdmission factory source).2.2.1

-- The same source event enters the receiver, survives paid prefixes, and is retained by the real Feed.
theorem source_in_born (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):
 (show Prop from by
  rcases source with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
  cases language
  let packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot):=
   ⟨n,⟨frame,seed⟩,⟨A.X,datum,scalar,pair⟩,⟨rfl⟩⟩
  let native:=AS.nativeAfterAdmission factory packet
  exact ∀event∈(A.nativeWordInventory observation nontrivial half n frame).trace,
   event∈(AN.bornStock (selected native) native.2.2.1).trace):=by
 rcases source with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
 cases language
 let cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot):=⟨A.X,datum,scalar,pair⟩
 let packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot):=⟨n,⟨frame,seed⟩,cfg,⟨rfl⟩⟩
 let native:=AS.nativeAfterAdmission factory packet
 change ∀event∈(A.nativeWordInventory observation nontrivial half n frame).trace,
  event∈(AN.bornStock (selected native) native.2.2.1).trace
 have kept:=Generic.paid_prefix_inventory native.2.1.1 (AS.stockCfg native.2.2.1)
  (AS.localNativeReceipt native).1 (Nat.le_refl _)
 change (selected native).inventory=native.2.1.1.inventory at kept
 intro event present
 apply Feed.original_preserved
 unfold AS.stockScalar
 rw [kept]
 apply preserve_carried
 exact source_in_scalar observation nontrivial half packet event present

def bornRelation (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):
 Σ' relation:(actualBornHistory observation nontrivial half source).relationClosure,
 HEq relation.val (A.nativeWordData observation nontrivial half source.1 source.2.1.1).gamma:=by
 rcases source with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
 cases language
 let cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot):=⟨A.X,datum,scalar,pair⟩
 let packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot):=⟨n,⟨frame,seed⟩,cfg,⟨rfl⟩⟩
 let word:=A.nativeWordData observation nontrivial half n frame
 refine ⟨⟨word.gamma,?_⟩,HEq.rfl⟩
 have source:=word.relation.property
 rw [word.relation_source] at source
 exact P.relations_next _ _ _ _ (source_in_born observation nontrivial half packet) source

def actualBornRelation (update cutoff:Nat):
 Σ' relation:(actualBornHistory observation nontrivial half
   (source observation nontrivial half depth ordinal update cutoff)).relationClosure,
 HEq relation.val (actualGamma observation nontrivial half depth ordinal update cutoff):=
 let written:=bornRelation observation nontrivial half
  (source observation nontrivial half depth ordinal update cutoff)
 ⟨written.1,written.2.trans
  (heq_of_eq (actual_gamma_source observation nontrivial half depth ordinal update cutoff).symm)⟩

theorem actual_word_normalized (update cutoff:Nat):
 actualGamma observation nontrivial half depth ordinal update cutoff=
 (datum observation nontrivial half depth ordinal update cutoff).omega-
  constantMap (R:=ℤ) (Value:=PairValue (Lower.Value A.W (source observation nontrivial half depth ordinal update cutoff).1))
   (Var:=A.X) (s:=slot) (actualNu observation nontrivial half depth ordinal update cutoff):=
 (actual_gamma_source observation nontrivial half depth ordinal update cutoff).trans
  ((produced_normalized (datum observation nontrivial half depth ordinal update cutoff)).trans
   (congrArg (fun nu:PairValue (Lower.Value A.W (source observation nontrivial half depth ordinal update cutoff).1) slot→₀ℤ=>
     (datum observation nontrivial half depth ordinal update cutoff).omega-
      constantMap (R:=ℤ) (Value:=PairValue (Lower.Value A.W (source observation nontrivial half depth ordinal update cutoff).1))
       (Var:=A.X) (s:=slot) nu)
    (actual_nu_source observation nontrivial half depth ordinal update cutoff)).symm)

namespace PairTransport
variable {Sorts:Type} {U X:Sorts→Type} [∀t,AddCommGroup (U t)] {s:Sorts}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=U) (Var:=X) (sort:=s))
variable (carried:RootedAccountedUnfolding (PresentedRelationEventAt (Expr U X s)))
variable (registered:frame.inventory=some carried)
include registered

private theorem event_next (event:PresentedRelationEventAt (Expr U X s)) (present:event∈carried.trace):
 Res.liftEvent event∈(J.completeWrittenInventory (I.seed frame) (Act.epoch frame) (S.actualOccurrence frame)).trace:=by
 have prior:event∈(IP.priorSeed (I.seed frame) (Act.epoch frame)).trace:=by
  unfold IP.priorSeed
  rw [show (Act.epoch frame).inventory=some carried from registered]
  exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
 have updated:event∈(IP.updatedSeed (I.seed frame) (Act.epoch frame) (S.actualOccurrence frame)).trace:=
  (SourceHistoryCommon.parallel_left _ _ _).1 event prior
 have lifted:Res.liftEvent event∈(Res.liftedInventory (I.seed frame) (Act.epoch frame) (S.actualOccurrence frame)).trace:=by
  change Res.liftEvent event∈((IP.updatedSeed (I.seed frame) (Act.epoch frame) (S.actualOccurrence frame)).map Res.liftEvent).trace
  rw [Stock.mapped_trace]
  exact List.mem_map_of_mem updated
 have previous:Res.liftEvent event∈(Res.priorPairInventory (I.seed frame) (Act.epoch frame) (S.actualOccurrence frame)).trace:=by
  unfold Res.priorPairInventory
  split
  · exact lifted
  · exact (SourceHistoryCommon.parallel_right _ _ _).1 _ lifted
 apply J.complete_written_preserves
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ previous

theorem relation_next (word:Formal ℤ U X s)
 (present:word∈SourceInventoryExecutionFeed.relationSpace carried):
 liftMap (R:=ℤ) word∈SourceInventoryExecutionFeed.relationSpace
  (J.completeWrittenInventory (I.seed frame) (Act.epoch frame) (S.actualOccurrence frame)):=by
 apply Submodule.span_induction (R:=ℤ) (p:=fun word _=>liftMap (R:=ℤ) word∈SourceInventoryExecutionFeed.relationSpace
  (J.completeWrittenInventory (I.seed frame) (Act.epoch frame) (S.actualOccurrence frame)))
 · intro relation present
   exact Submodule.subset_span (event_next frame carried registered (.relation relation) present)
 · simpa only [map_zero] using (Submodule.zero_mem _)
 · intro left right _ _ leftMem rightMem
   simpa only [map_add] using Submodule.add_mem _ leftMem rightMem
 · intro scalar word _ member
   simpa only [map_smul] using Submodule.smul_mem _ scalar member
 · exact present
end PairTransport

private def bornFrame (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):=
 (AS.bornAfterNative (AS.nativeAfterAdmission factory source)).2.1.1

private def jointInventoryAt (packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):=
 J.completeWrittenInventory (I.seed packet.2.1.1) (Act.epoch packet.2.1.1)
  (S.actualOccurrence packet.2.1.1)
private def jointHistoryAt (packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):=
 P.prefixHistory ((jointInventoryAt packet).map (fun event=>(S.actualOccurrence packet.2.1.1,event)))
  (jointInventoryAt packet)
def nextJointInventory (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):=
 jointInventoryAt (AS.bornAfterNative (AS.nativeAfterAdmission factory source))
def nextJointHistory (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):=
 jointHistoryAt (AS.bornAfterNative (AS.nativeAfterAdmission factory source))

def nextJointRelation (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):
 Σ' relation:(nextJointHistory observation nontrivial half source).relationClosure,
 HEq relation.val (liftMap (R:=ℤ) (bornRelation observation nontrivial half source).1.val):=by
 let native:=AS.nativeAfterAdmission factory source
 let frame:=selected native
 let carried:=AN.bornStock frame native.2.2.1
 let word:=(bornRelation observation nontrivial half source).1
 have registered:(bornFrame observation nontrivial half source).inventory=some carried:=rfl
 have belongs:word.val∈SourceInventoryExecutionFeed.relationSpace carried:=by
  simpa only [actualBornHistory,AN.bornHistory,Feed.history_relation_space] using word.property
 refine ⟨⟨liftMap (R:=ℤ) word.val,?_⟩,HEq.rfl⟩
 simpa only [nextJointHistory,jointHistoryAt,jointInventoryAt,bornFrame,Feed.history_relation_space] using
  PairTransport.relation_next (bornFrame observation nontrivial half source) carried registered word.val belongs

private def transport_joint_relation
 {before after:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)} (same:before=after)
 (relation:(jointHistoryAt before).relationClosure):
 Σ' written:(jointHistoryAt after).relationClosure,HEq written.val relation.val:=by
 cases same
 exact ⟨relation,HEq.rfl⟩

theorem actual_born_packet (update cutoff:Nat):
 AS.bornAfterNative (AS.nativeAfterAdmission factory
  (source observation nontrivial half depth ordinal update cutoff))=
 D.packetAt factory initial pR rfl (update+2):=
 (congrArg (fun packet=>AS.bornAfterNative (AS.nativeAfterAdmission factory packet))
  (installedMethod observation nontrivial half depth ordinal update cutoff).method.source_literal).trans
 (D.packetAt_successor factory initial pR rfl (update+1)).symm

def actualNextJointReceipt (update cutoff:Nat):=
 transport_joint_relation (actual_born_packet observation nontrivial half depth ordinal update cutoff)
  (nextJointRelation observation nontrivial half
   (source observation nontrivial half depth ordinal update cutoff)).1

theorem actualNextJoint_value (update cutoff:Nat):
 HEq (actualNextJointReceipt observation nontrivial half depth ordinal update cutoff).1.val
  (liftMap (R:=ℤ) (bornRelation observation nontrivial half
   (source observation nontrivial half depth ordinal update cutoff)).1.val):=
 (actualNextJointReceipt observation nontrivial half depth ordinal update cutoff).2.trans
  (nextJointRelation observation nontrivial half
   (source observation nontrivial half depth ordinal update cutoff)).2

-- Both quotient zero and the original noncollapsed value word are kept; no physical increment is set to zero.
set_option cleanup.letToHave false in
noncomputable def actual_R_word_Pa_writeback (update cutoff:Nat):=
 PProd.mk (installedMethod observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (observedTrace observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actualNu observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actualGamma observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actualInventory observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (source_in_born observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)) <|
 PProd.mk (actual_effect_source observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actual_word_bill observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actual_word_fee observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (TraceFaces.actual_effect
  (compiledOccurrence observation nontrivial half depth ordinal update cutoff)
  (observedTrace observation nontrivial half depth ordinal update cutoff)) <|
 PProd.mk (TraceFaces.whole_recovery
  (compiledOccurrence observation nontrivial half depth ordinal update cutoff)
  (observedTrace observation nontrivial half depth ordinal update cutoff)
  (datum observation nontrivial half depth ordinal update cutoff).omega) <|
 PProd.mk (TraceFaces.whole_recovery
  (compiledOccurrence observation nontrivial half depth ordinal update cutoff)
  (observedTrace observation nontrivial half depth ordinal update cutoff)
  (constantMap (R:=ℤ) (Value:=PairValue (Lower.Value A.W (source observation nontrivial half depth ordinal update cutoff).1))
   (Var:=A.X) (s:=slot) (actualNu observation nontrivial half depth ordinal update cutoff))) <|
 PProd.mk (TraceFaces.whole_recovery
  (compiledOccurrence observation nontrivial half depth ordinal update cutoff)
  (observedTrace observation nontrivial half depth ordinal update cutoff)
  (actualGamma observation nontrivial half depth ordinal update cutoff)) <|
 PProd.mk (actual_word_normalized observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actualBornRelation observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (nextJointRelation observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)) <|
 PProd.mk (actual_born_packet observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actualNextJointReceipt observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (actualNextJoint_value observation nontrivial half depth ordinal update cutoff) <|
 PProd.mk (Cx.completion_kills_generated_differential
  (jointHistoryAt (D.packetAt factory initial pR rfl (update+2)))
  (actualNextJointReceipt observation nontrivial half depth ordinal update cutoff).1) <|
 PProd.mk (J.disposition (I.seed (bornFrame observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)))
  (Act.epoch (bornFrame observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)))
  (S.actualOccurrence (bornFrame observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)))) <|
 PProd.mk (Cx.completion_kills_generated_differential
  (nextJointHistory observation nontrivial half (source observation nontrivial half depth ordinal update cutoff))
  (nextJointRelation observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)).1) <|
 PProd.mk (Cx.natComplex (actualBornHistory observation nontrivial half (source observation nontrivial half depth ordinal update cutoff))) <|
 PProd.mk (Cx.completion_kills_generated_differential
  (actualBornHistory observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)) (actualBornRelation observation nontrivial half depth ordinal update cutoff).1) <|
 PProd.mk (M.actual_source_method_step observation nontrivial half depth ordinal (update+1))
  (D.history_end_index factory initial pR rfl (update+1))

end CountedPaInitial.BornRWordPaWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
