import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativePaInstall.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open private raw retainedCode pairAction from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCanonicalMethodRuntime
open private read_price_pair read_price_pair_source PriceRowReceipt PriceRowReceipt.state from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSourcePrice.Consumer
open private PricePaPayload from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativePaInstall.Consumer
open private terminalTrace terminalTrace_natural from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Source
namespace TraceFaces
variable {Root Sorts:Type} {V X:Sorts→Type} [∀t,AddCommGroup (V t)] {s:Sorts}
variable {E:Env V X} {operation:V s→+V s} {input:Expr V X s} {result:V s}
variable (occurrence:Root) (trace:Trace E (.linear operation input) (.const result))
def occurrenceTree:=(traceInventory trace).map (fun event=>(occurrence,event))
abbrev sourceHistory:=P.prefixHistory (occurrenceTree occurrence trace) (traceInventory trace)
def relation:(sourceHistory occurrence trace).relationClosure:=by
 refine ⟨traceGamma trace,?_⟩
 have whole_kept : ∀ event ∈ (P.exposure trace).trace, event ∈ (traceInventory trace).trace := by
  intro event present
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event
   ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
 have child_kept : ∀ event ∈ (P.exposure (SourceOperationExecution.originalInput trace).2.1).trace,
   event ∈ (traceInventory trace).trace := by
  intro event present
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event
   ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
 apply Submodule.sub_mem
 · exact P.relations_next _ _ _ _ whole_kept
    (P.boundary_in_inventory (occurrenceTree occurrence trace) trace)
 · exact P.relations_next _ _ _ _ child_kept
    (P.boundary_in_inventory (occurrenceTree occurrence trace) (SourceOperationExecution.originalInput trace).2.1)
def sourceComplex:=Cx.natComplex (sourceHistory occurrence trace)
def effectInput:=({
 occurrence:=occurrenceTree occurrence trace
 algebraAt:=fun point=>(point,traceNu trace,traceGamma trace)
 combinatorialAt:=fun point=>(point,trace,SourceOperationExecution.originalInput trace,traceInventory trace)
 topologicalAt:=fun point=>(point,CofinalAllPrimeTopology.TopologicalAt.generate (sourceHistory occurrence trace))
 logicalAt:=fun point=>(point,PLift.up (fun degree:Nat=>CofinalRelationGeneratedComplex.differential_sq (sourceHistory occurrence trace) degree))
 relationAt:=fun point=>(point,relation occurrence trace)
 cochainAt:=fun point=>(point,sourceComplex occurrence trace)
 evaluationAt:=fun _=>evaluation (R:=ℤ) E
 faithfulAt:=fun _=>LinearMap.id
 } :UnifiedFourFace.Evaluation.Input _ _ _ _ _ _ _ (Formal ℤ V X s) (V s))
def effectFaces:=UnifiedFourFace.Evaluation.generate (effectInput occurrence trace)
def wholeInput:=({
 occurrence:=occurrenceTree occurrence trace
 algebraAt:=fun point=>(point,traceNu trace,traceGamma trace)
 combinatorialAt:=fun point=>(point,trace,SourceOperationExecution.originalInput trace,traceInventory trace)
 topologicalAt:=fun point=>(point,CofinalAllPrimeTopology.TopologicalAt.generate (sourceHistory occurrence trace))
 logicalAt:=fun point=>(point,PLift.up (fun degree:Nat=>CofinalRelationGeneratedComplex.differential_sq (sourceHistory occurrence trace) degree))
 relationAt:=fun point=>(point,relation occurrence trace)
 cochainAt:=fun point=>(point,sourceComplex occurrence trace)
 dualEvaluationAt:=fun _=>SourceGeneratedCompleteWordDual.pairing
 faithfulAt:=fun _=>LinearMap.id
 } :UnifiedFourFace.Input _ _ _ _ _ _ _ (Formal ℤ V X s) (Formal ℤ V X s))
def wholeFaces:=UnifiedFourFace.generate (wholeInput occurrence trace)
theorem actual_effect:
 (effectFaces occurrence trace).embedding ((effectFaces occurrence trace).canonical
  (Finsupp.single (.linear operation input) 1-Finsupp.single input 1))=
 ScalarRelationPresentation.freeEvaluation (R:=ℤ) (V s) (traceNu trace):=by
 have applied:=LinearMap.congr_fun
  (UnifiedFourFace.Evaluation.embedding_canonical (effectInput occurrence trace))
  (Finsupp.single (.linear operation input) 1-Finsupp.single input 1)
 have values:=LinearMap.congr_fun (valueMap_evaluation (R:=ℤ) (s:=s) E)
  (Finsupp.single (.linear operation input) 1-Finsupp.single input 1)
 rw [trace_nu_source]
 exact applied.trans values.symm

theorem whole_recovery (word:Formal ℤ V X s):
 SourceGeneratedCompleteWordDual.coimageRecovery ((wholeFaces occurrence trace).canonical word)=word:=
 SourceGeneratedCompleteWordDual.recovery_source word
end TraceFaces

namespace A
export BornRCanonicalMethodRuntime (W X actionAt nativeStock fixedRFactory nativeWordData nativeWordInventory sourceRuntime)
end A
namespace Lower
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end Lower
namespace Native
export BornRNativePaInstall (actual_installed_Pa_dynamics_price)
end Native
namespace M
export BornRSealedMethodHistory (wholeProjection wholeProjection_action packetStock actualStock actualStock_step actual_source_method_step)
end M
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative scalar stockScalar stockCfg localNativeReceipt)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor historyAt history_end_index actual_index)
end D
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base baseRoot actualVisit actualOccurrence frames next nextBorn)
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_paid_prefix)
end Prefix
end S
namespace AN
export ActualNativeRelationTransport (bornStock born_stock bornHistory)
end AN
namespace Feed
export SourceInventoryExecutionFeed (original_preserved history_relation_space)
end Feed
local instance levelGroups (n:Nat):∀t,AddCommGroup
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value A.W n t):=
 BornRCanonicalMethodRuntime.levelGroups n
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "slot"=>CompletedSourceRCalculation.Slot.branches
local notation "factory"=>A.fixedRFactory observation nontrivial half
local notation "initial"=>H.receiver observation nontrivial half depth ordinal
local notation "pR"=>H.methodProgramme observation nontrivial half depth ordinal

private abbrev CompiledPairAt
 {Parent:Sort uParent} {Index:Sort uIndex} {Whole:Sort uWhole} {Next:Sort uNext}
 {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory} {update cutoff:Nat}
 (method:BornRSourcePrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index)
  (Whole:=Whole) (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff):=
 PProd
  (SourceOperationExecutionDebt.State
   (SourceGeneratedInquiryReceiptAction.actionReader method.source.2.1.1 method.source.2.2.1
    (S.actualOccurrence method.source.2.1.1)).environment
   (SourceGeneratedInquiryReceiptAction.actionReader method.source.2.1.1 method.source.2.2.1
    (S.actualOccurrence method.source.2.1.1)).expression)
  (PricePaPayload observation nontrivial half method.source method.native cutoff)

private def read_pair_at_method
 {Parent:Sort uParent} {Index:Sort uIndex} {Whole:Sort uWhole} {Next:Sort uNext}
 {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory} {update cutoff:Nat}
 (method:BornRSourcePrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index)
  (Whole:=Whole) (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff):
 CompiledPairAt observation nontrivial half depth ordinal method:=
 read_price_pair method.price_method.2.1

def installedMethod (update cutoff:Nat):=Native.actual_installed_Pa_dynamics_price
 observation nontrivial half depth ordinal update cutoff
attribute [local irreducible] installedMethod
private def source (update cutoff:Nat):=(installedMethod observation nontrivial half depth ordinal update cutoff).method.source
private def datum (update cutoff:Nat):=A.nativeWordData observation nontrivial half
 (source observation nontrivial half depth ordinal update cutoff).1
 (source observation nontrivial half depth ordinal update cutoff).2.1.1
private def compiledPair (update cutoff:Nat):
 CompiledPairAt observation nontrivial half depth ordinal
  (installedMethod observation nontrivial half depth ordinal update cutoff).method:=
 read_pair_at_method observation nontrivial half depth ordinal
  (installedMethod observation nontrivial half depth ordinal update cutoff).method

namespace OwnSource
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
 (state visit answerFace endpointCount actual_state endpoint_source_state)
end OwnSource

private def actionTerminalAt (n:Nat)
 (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Lower.Value A.W n) (Var:=A.X) (sort:=slot))
 (cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot)):=
 let root:=(S.baseRoot frame cfg).toAuthoritativeRoot
 let origin:=(S.actualVisit frame).current
 let reader:root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin→
  OF.Raw (Value:=PairValue (Lower.Value A.W n)) (Var:=cfg.LowVar) (sort:=slot):=
  fun _=>SourceGeneratedInquiryReceiptAction.actionReader frame cfg (S.actualOccurrence frame)
 OF.runtimeCurrent root origin reader (OF.Calc.targetRuntime root origin reader)

set_option maxHeartbeats 12000 in
private theorem action_state_source (n:Nat)
 (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Lower.Value A.W n) (Var:=A.X) (sort:=slot))
 (cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot))
 (language:cfg.LowVar=A.X)
 (reader:HEq (SourceGeneratedInquiryReceiptAction.actionReader frame cfg (S.actualOccurrence frame))
  (raw observation nontrivial half n frame)):
 HEq (actionTerminalAt n frame cfg)
  (A.nativeWordData observation nontrivial half n frame).state:=by
 rcases cfg with ⟨Y,read,scalar,pair⟩
 cases language
 let next:=(S.baseRoot frame (⟨A.X,read,scalar,pair⟩)).toAuthoritativeRoot
 let origin:=(S.actualVisit frame).current
 let operation:=@pairAction (Lower.Value A.W n slot) (Lower.groups A.W n slot)
  (A.actionAt observation nontrivial half n)
 let input:=liftExpr (retainedCode n frame)
 have natural:=source_state_natural (Value:=PairValue (Lower.Value A.W n))
  (Var:=A.X) (s:=slot) (S.base frame).root.toAuthoritativeRoot origin
  (raw observation nontrivial half n frame).environment operation input next
 let runRaw:=fun sourceRaw:OF.Raw (Value:=PairValue (Lower.Value A.W n)) (Var:=A.X) (sort:=slot)=>
  OF.runtimeCurrent next origin (fun _=>sourceRaw) (OF.Calc.targetRuntime next origin (fun _=>sourceRaw))
 let actualRaw:=SourceGeneratedInquiryReceiptAction.actionReader frame
  (⟨A.X,read,scalar,pair⟩) (S.actualOccurrence frame)
 have rawEq:actualRaw=raw observation nontrivial half n frame:=eq_of_heq reader
 have rawState:HEq (runRaw actualRaw) (runRaw (raw observation nontrivial half n frame)):=
  @Eq.rec _ actualRaw (fun sourceRaw _=>HEq (runRaw actualRaw) (runRaw sourceRaw))
   HEq.rfl (raw observation nontrivial half n frame) rawEq
 exact (rawState.trans (heq_of_eq natural.symm)).trans
  (heq_of_eq (A.nativeWordData observation nontrivial half n frame).state_source.symm)

set_option maxHeartbeats 12000 in
private theorem receipt_endpoint_at_root
 {NW:WorldRelationNetwork} {Voc:Vocabulary}
 (root:SourceNativeLivingRootClosure NW Voc)
 (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
 (U7:U7ProducerCalculus NW) (calculus:U7ObstructionEvolutionCalculus NW U7)
 {Sorts:Type} {Value Var:Sorts→Type} [∀t,AddCommGroup (Value t)] {s:Sorts}
 (reader:root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current→
  OF.Raw (Value:=Value) (Var:=Var) (sort:=s))
 {Payload:Type} {value:Payload}
 (receipt:PriceRowReceipt (OwnSource.state root visit U7 calculus reader
  (OwnSource.endpointCount root visit reader)) PUnit.unit Payload value):
 HEq (read_price_pair receipt).1
  (OF.runtimeCurrent root.toAuthoritativeRoot visit.current reader
   (OF.Calc.targetRuntime root.toAuthoritativeRoot visit.current reader)):=by
 let count:=OwnSource.endpointCount root visit reader
 have first:=congrArg
  (fun pair:PProd (OF.Current root.toAuthoritativeRoot visit.current reader) Payload=>pair.1)
  (read_price_pair_source receipt)
 dsimp only [OwnSource.state] at first
 have faceRead:=OwnSource.actual_state root visit U7 calculus reader count
 have endpoint:=OwnSource.endpoint_source_state root visit U7 calculus reader
 exact (heq_of_eq first).trans ((heq_of_eq faceRead.symm).trans (heq_of_eq endpoint))

set_option maxHeartbeats 12000 in
private theorem compiled_state_at_method
 {Parent:Sort uParent} {Index:Sort uIndex} {Whole:Sort uWhole} {Next:Sort uNext}
 {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory} {update cutoff:Nat}
 (method:BornRSourcePrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index)
  (Whole:=Whole) (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff):
 HEq (read_pair_at_method observation nontrivial half depth ordinal method).1
  (A.nativeWordData observation nontrivial half method.source.1 method.source.2.1.1).state:=by
 let frame:=method.source.2.1.1
 let cfg:=method.source.2.2.1
 let root:=S.baseRoot frame cfg
 let visit:=S.actualVisit frame
 let state:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.state frame cfg
 let reader:root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current→
  OF.Raw (Value:=PairValue (Lower.Value A.W method.source.1)) (Var:=cfg.LowVar) (sort:=slot):=
  fun _=>SourceGeneratedInquiryReceiptAction.actionReader frame cfg (S.actualOccurrence frame)
 have original:=receipt_endpoint_at_root root visit state.U7 state.calculus reader method.price_method.2.1
 have source:=action_state_source observation nontrivial half method.source.1 frame cfg
  method.source.2.2.2.down method.source_reader
 exact original.trans source

set_option maxHeartbeats 12000 in
private abbrev compiled_state_source (update cutoff:Nat):=
 compiled_state_at_method observation nontrivial half depth ordinal
  (installedMethod observation nontrivial half depth ordinal update cutoff).method

private def observedState (update cutoff:Nat):type_of% (datum observation nontrivial half depth ordinal update cutoff).state:=
 cast (type_eq_of_heq (compiled_state_source observation nontrivial half depth ordinal update cutoff))
  (compiledPair observation nontrivial half depth ordinal update cutoff).1
private theorem observed_state_source (update cutoff:Nat):
 observedState observation nontrivial half depth ordinal update cutoff=
 (datum observation nontrivial half depth ordinal update cutoff).state:=
 eq_of_heq ((cast_heq _ _).trans
  (compiled_state_source observation nontrivial half depth ordinal update cutoff))
private def observedTrace (update cutoff:Nat):type_of% (datum observation nontrivial half depth ordinal update cutoff).trace:=
 terminalTrace (observedState observation nontrivial half depth ordinal update cutoff)
  ((congrArg Sigma.fst (observed_state_source observation nontrivial half depth ordinal update cutoff)).trans
   (datum observation nontrivial half depth ordinal update cutoff).state_endpoint)
private def occurrence_at_method
 {Parent:Sort uParent} {Index:Sort uIndex} {Whole:Sort uWhole} {Next:Sort uNext}
 {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory} {update cutoff:Nat}
 (method:BornRSourcePrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index)
  (Whole:=Whole) (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff):=
 let state:=PriceRowReceipt.state method.price_method.2.1
 state.root.emitted state.visit.current

set_option cleanup.letToHave false in
private def compiledOccurrence (update cutoff:Nat):=
 occurrence_at_method observation nontrivial half depth ordinal
  (installedMethod observation nontrivial half depth ordinal update cutoff).method

def actualEffectFaces (update cutoff:Nat):=
 TraceFaces.effectFaces (compiledOccurrence observation nontrivial half depth ordinal update cutoff)
  (observedTrace observation nontrivial half depth ordinal update cutoff)
def actualWholeFaces (update cutoff:Nat):=
 TraceFaces.wholeFaces (compiledOccurrence observation nontrivial half depth ordinal update cutoff)
  (observedTrace observation nontrivial half depth ordinal update cutoff)

def actualNu (update cutoff:Nat):=traceNu (observedTrace observation nontrivial half depth ordinal update cutoff)
def actualGamma (update cutoff:Nat):=traceGamma (observedTrace observation nontrivial half depth ordinal update cutoff)
def actualInventory (update cutoff:Nat):=traceInventory (observedTrace observation nontrivial half depth ordinal update cutoff)

private theorem produced_trace_readback
 {Sorts:Type} {Value Var:Sorts→Type} [∀t,AddCommGroup (Value t)] {s:Sorts}
 {NW:WorldRelationNetwork} {Voc:Vocabulary}
 {old:SourceNativeAuthoritativeRootClosure NW Voc} {origin:Voc.Current}
 {env:Env Value Var} {operation:Value s→+Value s} {input:Expr Value Var s}
 (data:Produced old origin env operation input)
 (observed:SourceOperationExecutionDebt.State env (.linear operation input))
 (same:observed=data.state)
 (endpoint:observed.1=.const (operation (input.eval env))):
 terminalTrace observed endpoint=data.trace:=by
 rw [data.trace_source]
 unfold sourceTrace
 exact terminalTrace_natural _ _ _ _ (same.trans data.state_source)

private theorem observed_trace_source (update cutoff:Nat):
 observedTrace observation nontrivial half depth ordinal update cutoff=
 (datum observation nontrivial half depth ordinal update cutoff).trace:=
 produced_trace_readback (datum observation nontrivial half depth ordinal update cutoff)
  (observedState observation nontrivial half depth ordinal update cutoff)
  (observed_state_source observation nontrivial half depth ordinal update cutoff)
  ((congrArg Sigma.fst (observed_state_source observation nontrivial half depth ordinal update cutoff)).trans
   (datum observation nontrivial half depth ordinal update cutoff).state_endpoint)

private theorem produced_nu_readback
 {Sorts:Type} {Value Var:Sorts→Type} [∀t,AddCommGroup (Value t)] {s:Sorts}
 {NW:WorldRelationNetwork} {Voc:Vocabulary}
 {old:SourceNativeAuthoritativeRootClosure NW Voc} {origin:Voc.Current}
 {env:Env Value Var} {operation:Value s→+Value s} {input:Expr Value Var s}
 (data:Produced old origin env operation input):traceNu data.trace=data.nu:=by
 rw [data.trace_source,data.nu_source]
 exact trace_nu_source _

private theorem produced_gamma_readback
 {Sorts:Type} {Value Var:Sorts→Type} [∀t,AddCommGroup (Value t)] {s:Sorts}
 {NW:WorldRelationNetwork} {Voc:Vocabulary}
 {old:SourceNativeAuthoritativeRootClosure NW Voc} {origin:Voc.Current}
 {env:Env Value Var} {operation:Value s→+Value s} {input:Expr Value Var s}
 (data:Produced old origin env operation input):traceGamma data.trace=data.gamma:=by
 rw [data.trace_source,data.gamma_source]
 rfl

private theorem produced_inventory_readback
 {Sorts:Type} {Value Var:Sorts→Type} [∀t,AddCommGroup (Value t)] {s:Sorts}
 {NW:WorldRelationNetwork} {Voc:Vocabulary}
 {old:SourceNativeAuthoritativeRootClosure NW Voc} {origin:Voc.Current}
 {env:Env Value Var} {operation:Value s→+Value s} {input:Expr Value Var s}
 (data:Produced old origin env operation input):traceInventory data.trace=data.inventory:=by
 rw [data.trace_source,data.inventory_source]
 rfl

theorem actual_nu_source (update cutoff:Nat):
 actualNu observation nontrivial half depth ordinal update cutoff=
 (datum observation nontrivial half depth ordinal update cutoff).nu:=
 (congrArg traceNu (observed_trace_source observation nontrivial half depth ordinal update cutoff)).trans
  (produced_nu_readback (datum observation nontrivial half depth ordinal update cutoff))

theorem actual_gamma_source (update cutoff:Nat):
 actualGamma observation nontrivial half depth ordinal update cutoff=
 (datum observation nontrivial half depth ordinal update cutoff).gamma:=
 (congrArg traceGamma (observed_trace_source observation nontrivial half depth ordinal update cutoff)).trans
  (produced_gamma_readback (datum observation nontrivial half depth ordinal update cutoff))

theorem actual_inventory_source (update cutoff:Nat):
 actualInventory observation nontrivial half depth ordinal update cutoff=
 A.nativeWordInventory observation nontrivial half
  (source observation nontrivial half depth ordinal update cutoff).1
  (source observation nontrivial half depth ordinal update cutoff).2.1.1:=
 (congrArg traceInventory (observed_trace_source observation nontrivial half depth ordinal update cutoff)).trans
  ((produced_inventory_readback (datum observation nontrivial half depth ordinal update cutoff)).trans
   (datum observation nontrivial half depth ordinal update cutoff).inventory_source)

private theorem pair_projection_sub (n:Nat)
 (left right:PairValue (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value A.W n) slot):
 M.wholeProjection (n+1) (left-right)=M.wholeProjection (n+1) left-M.wholeProjection (n+1) right:=by
 induction n with
 | zero=>rfl
 | succ n previous=>exact previous left.1 right.1

private theorem source_nu_projection (packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):
 M.wholeProjection (packet.1+1)
  (ScalarRelationPresentation.freeEvaluation (R:=ℤ) _ (A.nativeWordData observation nontrivial half packet.1 packet.2.1.1).nu)=
 OriginalKFullSourceRAction.variableAction observation nontrivial half (A.nativeStock packet.1 packet.2.1.1)-
 A.nativeStock packet.1 packet.2.1.1:=by
 let n:=packet.1
 let frame:=packet.2.1.1
 let old:=(S.base frame).root.toAuthoritativeRoot
 let origin:=(S.actualVisit frame).current
 let env:=(raw observation nontrivial half n frame).environment
 let operation:=@pairAction _ (BornRCanonicalMethodRuntime.levelGroups n slot)
  (A.actionAt observation nontrivial half n)
 let input:=liftExpr (retainedCode n frame)
 have value:=free_value old origin env operation input
 have borrow:=(inputTrace old origin env operation input).sound
 have paired:=BornRSourceMethodConsumer.Generic.pair_zero (retainedCode n frame) frame.registered.input.environment
 have actualInput:(original old origin env operation input).1=
  ((retainedCode n frame).eval frame.registered.input.environment,0):=borrow.symm.trans paired
 rw [actualInput] at value
 have projected:=congrArg (M.wholeProjection (n+1)) value
 rw [pair_projection_sub n
  (operation ((retainedCode n frame).eval frame.registered.input.environment,0))
  ((retainedCode n frame).eval frame.registered.input.environment,0)] at projected
 have action:=M.wholeProjection_action observation nontrivial half n
  ((retainedCode n frame).eval frame.registered.input.environment)
 change M.wholeProjection (n+1)
   (ScalarRelationPresentation.freeEvaluation (R:=ℤ)
    (PairValue (Lower.Value A.W n) slot)
    (A.nativeWordData observation nontrivial half n frame).nu)=
  OriginalKFullSourceRAction.variableAction observation nontrivial half
   (A.nativeStock n frame)-A.nativeStock n frame
 simpa [A.nativeWordData,material,A.nativeStock,operation,n,frame,map_zero] using
  projected.trans (congrArg (fun value=>value-A.nativeStock n frame) action)


end CountedPaInitial.BornRWordPaWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
