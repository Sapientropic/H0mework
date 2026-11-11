import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativePaInstall.Source
import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Calculation

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw Current raw runtimeCurrent authoritativeRoot)
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation
 (targetRuntime completed target_state completed_value)
end Calc
namespace Completion
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion
 (state completedState completed initial_state next_state)
end Completion
end OF
namespace P
export SourceOperationPaidRelations
 (exposure prefixHistory boundary_in_inventory relations_next)
end P
namespace Cx
export CofinalRelationGeneratedComplex
 (natComplex natComplex_d_zero_one completion_kills_generated_differential)
end Cx

section TraceSource
variable {S:Type u} {Value Var:S→Type u} [∀t,AddCommGroup (Value t)] {s:S}
variable {environment:Env Value Var} {operation:Value s→+Value s} {input:Expr Value Var s} {result:Value s}
variable (trace:Trace environment (.linear operation input) (.const result))
def traceNu:Value s→₀ℤ:=Finsupp.single result 1-Finsupp.single (SourceOperationExecution.originalInput trace).1 1
def traceGamma:Formal ℤ Value Var s:=
 relationMap (R:=ℤ) environment (trace.relationWords (R:=ℤ))-
 relationMap (R:=ℤ) environment ((SourceOperationExecution.originalInput trace).2.1.relationWords (R:=ℤ))
def traceInventory:=SourceHistoryCommon.seed
 (SourceHistoryCommon.seed (P.exposure trace)
  (P.exposure (SourceOperationExecution.originalInput trace).2.1))
 (RootedAccountedUnfolding.zero
  (PresentedRelationEventAt.generator (Coefficients.expression (traceGamma trace))))

theorem trace_nu_source:
 traceNu trace=valueMap (R:=ℤ) environment
  (Finsupp.single (.linear operation input) 1-Finsupp.single input 1):=by
 have whole:=trace.sound
 have child:=(SourceOperationExecution.originalInput trace).2.1.sound
 simp [traceNu,valueMap,map_sub,whole,child]
 rfl
end TraceSource

section Source
variable {S:Type u} {Value Var:S→Type u} [∀t,AddCommGroup (Value t)] {s:S}
variable {NW:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
variable (old:SourceNativeAuthoritativeRootClosure NW V) (origin:V.Current)
variable (environment:Env Value Var) (operation:Value s→+Value s) (input:Expr Value Var s)

def sourceRaw:OF.Raw (Value:=Value) (Var:=Var) (sort:=s):=⟨environment,.linear operation input⟩
def sourceReader (_:old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin):=
 sourceRaw environment operation input

def sourceState:=OF.runtimeCurrent old origin (sourceReader old origin environment operation input)
 (OF.Calc.targetRuntime old origin (sourceReader old origin environment operation input))
def settlement:=OF.Calc.completed old origin (sourceReader old origin environment operation input)

private def terminalTrace {E:Env Value Var} {body:Expr Value Var s} {point:Value s}
 (state:SourceOperationExecutionDebt.State E body) (endpoint:state.1=.const point):
 Trace E body (.const point):=endpoint ▸ state.2

private theorem terminalTrace_natural {E:Env Value Var} {body:Expr Value Var s} {point:Value s}
 (first second:SourceOperationExecutionDebt.State E body)
 (firstEnd:first.1=.const point) (secondEnd:second.1=.const point) (same:first=second):
 terminalTrace first firstEnd=terminalTrace second secondEnd:=by
 cases same
 rfl

def sourceTrace:Trace environment (.linear operation input) (.const (operation (input.eval environment))):=by
 have endpoint:=(settlement old origin environment operation input).2.down
 have value:=OF.Calc.completed_value old origin (sourceReader old origin environment operation input)
 change (settlement old origin environment operation input).1=operation (input.eval environment) at value
 exact terminalTrace (sourceState old origin environment operation input)
  (endpoint.trans (congrArg Expr.const value))

theorem source_state_natural (next:SourceNativeAuthoritativeRootClosure NW V):
 sourceState old origin environment operation input=sourceState next origin environment operation input:=by
 unfold sourceState
 rw [OF.Calc.target_state,OF.Calc.target_state]
 exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_state old origin next origin
  (sourceRaw environment operation input) (remaining (.linear operation input))

theorem source_trace_natural (next:SourceNativeAuthoritativeRootClosure NW V):
 sourceTrace old origin environment operation input=sourceTrace next origin environment operation input:=by
 unfold sourceTrace
 exact terminalTrace_natural _ _ _ _ (source_state_natural old origin environment operation input next)

def original:=SourceOperationExecution.originalInput (sourceTrace old origin environment operation input)
def inputTrace:= (original old origin environment operation input).2.1

def omega:Formal ℤ Value Var s:=Finsupp.single (.linear operation input) 1-Finsupp.single input 1
def nu:Value s→₀ℤ:=valueMap (R:=ℤ) environment (omega operation input)
def gamma:Formal ℤ Value Var s:=
 relationMap (R:=ℤ) environment ((sourceTrace old origin environment operation input).relationWords (R:=ℤ))-
 relationMap (R:=ℤ) environment ((inputTrace old origin environment operation input).relationWords (R:=ℤ))

theorem free_value:
 ScalarRelationPresentation.freeEvaluation (R:=ℤ) (Value s) (nu environment operation input)=
 operation (original old origin environment operation input).1-(original old origin environment operation input).1:=by
 have full:=(sourceTrace old origin environment operation input).sound
 have borrowed:=(inputTrace old origin environment operation input).sound
 simpa [nu,omega,valueMap,ScalarRelationPresentation.freeEvaluation,Expr.eval,map_sub] using
  congrArg (fun value:Value s=>operation value-value) borrowed

theorem normalized_word:
 gamma old origin environment operation input=
 omega operation input-constantMap (R:=ℤ) (nu environment operation input):=by
 have full:=(sourceTrace old origin environment operation input).sound
 have borrowed:=(inputTrace old origin environment operation input).sound
 rw [gamma,(sourceTrace old origin environment operation input).relation_boundary,
  (inputTrace old origin environment operation input).relation_boundary]
 simp [omega,nu,valueMap,constantMap,Finsupp.mapDomain_sub,Finsupp.mapDomain_single,Expr.eval,borrowed]
 abel

/-- The original complete relation supplies the next literal query syntax. -/
def coefficientExpression:Expr Value Var s:=
 Coefficients.expression (gamma old origin environment operation input)

def inventory:=traceInventory (sourceTrace old origin environment operation input)

/-- The same source inventory contains the complete coefficient AST, alongside both paid traces. -/
theorem coefficient_generator:
 PresentedRelationEventAt.generator (coefficientExpression old origin environment operation input) ∈
  (inventory old origin environment operation input).trace:=
 (SourceHistoryCommon.parallel_right _ _ _).1 _ (RootedAccountedUnfolding.root_mem_trace _)

def rootOccurrence:=
 (P.exposure (sourceTrace old origin environment operation input)).map (fun event=>
  ((OF.authoritativeRoot old origin (sourceReader old origin environment operation input)).emitted
   (sourceState old origin environment operation input),event))
abbrev history:=P.prefixHistory (rootOccurrence old origin environment operation input)
 (inventory old origin environment operation input)

theorem source_events (event)
 (present:event∈(P.exposure (sourceTrace old origin environment operation input)).trace):
 event∈(inventory old origin environment operation input).trace:=
 (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_left _ _ _).1 event present)

theorem input_events (event)
 (present:event∈(P.exposure (inputTrace old origin environment operation input)).trace):
 event∈(inventory old origin environment operation input).trace:=
 (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_right _ _ _).1 event present)

def actualRelation:(history old origin environment operation input).relationClosure:=by
 refine ⟨gamma old origin environment operation input,?_⟩
 exact Submodule.sub_mem _
  (P.relations_next (rootOccurrence old origin environment operation input) (P.exposure (sourceTrace old origin environment operation input))
   (rootOccurrence old origin environment operation input) (inventory old origin environment operation input)
   (source_events old origin environment operation input)
   (P.boundary_in_inventory (rootOccurrence old origin environment operation input) (sourceTrace old origin environment operation input)))
  (P.relations_next (rootOccurrence old origin environment operation input) (P.exposure (inputTrace old origin environment operation input))
   (rootOccurrence old origin environment operation input) (inventory old origin environment operation input)
   (input_events old origin environment operation input)
   (P.boundary_in_inventory (rootOccurrence old origin environment operation input) (inputTrace old origin environment operation input)))

theorem gamma_sound:evaluation (R:=ℤ) environment (gamma old origin environment operation input)=0:=by
 rw [gamma,map_sub,
  (sourceTrace old origin environment operation input).relation_old (R:=ℤ),
  (inputTrace old origin environment operation input).relation_old (R:=ℤ)]
 exact sub_self _

abbrev complex:=Cx.natComplex (history old origin environment operation input)
theorem actual_differential:
 (((complex old origin environment operation input).d 0 1).hom
  (actualRelation old origin environment operation input)).val=gamma old origin environment operation input:=by
 rw [Cx.natComplex_d_zero_one]
 rfl

theorem completion_zero:
 (history old origin environment operation input).completionProjection
  (((complex old origin environment operation input).d 0 1).hom
   (actualRelation old origin environment operation input))=0:=
 Cx.completion_kills_generated_differential _ _

structure Produced where
 state:SourceOperationExecutionDebt.State environment (.linear operation input)
 state_source:state=sourceState old origin environment operation input
 state_endpoint:state.1=.const (operation (input.eval environment))
 trace:Trace environment (.linear operation input) (.const (operation (input.eval environment)))
 trace_source:trace=sourceTrace old origin environment operation input
 child:Σpoint:Value s,Trace environment input (.const point)×PLift (operation point=operation (input.eval environment))
 child_source:child=original old origin environment operation input
 omega:Formal ℤ Value Var s
 omega_source:omega=BornRWordPaWriteback.omega operation input
 nu:Value s→₀ℤ
 nu_source:nu=BornRWordPaWriteback.nu environment operation input
 gamma:Formal ℤ Value Var s
 gamma_source:gamma=BornRWordPaWriteback.gamma old origin environment operation input
 inventory:RootedAccountedUnfolding (PresentedRelationEventAt (Expr Value Var s))
 inventory_source:inventory=BornRWordPaWriteback.inventory old origin environment operation input
 relation:(history old origin environment operation input).relationClosure
 relation_source:relation.val=gamma

def material:Produced old origin environment operation input where
 state:=sourceState old origin environment operation input
 state_source:=rfl
 state_endpoint:=by
  have endpoint:=(settlement old origin environment operation input).2.down
  have value:=OF.Calc.completed_value old origin (sourceReader old origin environment operation input)
  exact endpoint.trans (congrArg Expr.const value)
 trace:=sourceTrace old origin environment operation input
 trace_source:=rfl
 child:=original old origin environment operation input
 child_source:=rfl
 omega:=omega operation input
 omega_source:=rfl
 nu:=nu environment operation input
 nu_source:=rfl
 gamma:=gamma old origin environment operation input
 gamma_source:=rfl
 inventory:=inventory old origin environment operation input
 inventory_source:=rfl
 relation:=actualRelation old origin environment operation input
 relation_source:=rfl
end Source
end CountedPaInitial.BornRWordPaWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
