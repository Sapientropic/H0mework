import H0mework.Foundation.Inquiry.Engine

/-!
# Canonical inquiry runtime

The inquiry engine already owns the exact U7-first resolution and its
source-generated successor, including a heterogeneous revised root after U8.
This runtime adds no scheduler or branch grammar. It seals the current engine
together with its source-generated activation; `tick` delegates to
`Engine.ask`, and the next activation is generated from that exact transition.

The fixed-root living runtime remains the micro-step runtime. This file is a
derived inquiry macro runtime: one tick may include the old-root write, U7,
minimal-coface U8, and the revised first write. Its next therefore must not be
replaced by the old fixed-law micro-successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootInquiryCompletion

universe u

/-- One fixed inquiry process together with its recursively generated
activation law. -/
structure SourceNativeInquiryRuntime
    (process : SourceNativeInquiryEngineProcess.{u}) : Type (u + 14) where
  activationLaw : Engine.SourceNativeInquiryActivationLaw process

namespace SourceNativeInquiryRuntime

/-- Reachable runtime state. The constructor is private: consumers cannot
pick an arbitrary hidden process state and mint an activation there. -/
structure State
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) : Type (u + 13) where
  private mk ::
  engine : Engine process
  activation : Engine.SourceNativeInquiryActivationAt engine

/-- Source-generated initial runtime state. -/
def initialState
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) : runtime.State :=
  ⟨Engine.initial process, runtime.activationLaw.initial⟩

/-- Authority-bearing inquiry macro occurrence at one reachable runtime
state.  The constructor stores no raw engine occurrence: every readout is
recomputed from the fixed runtime state.  Thus a sibling raw compiler may be
modelled, but it cannot be wrapped as this named runtime's authority. -/
structure ExactActivatedInquiryOccurrenceAt
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    (state : runtime.State) : Type (u + 13) where
  private mk ::

/-- Raw engine execution is a dependent readout of the sealed activation,
not an authority constructor. -/
def ExactActivatedInquiryOccurrenceAt.rawReadout
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (_activated : ExactActivatedInquiryOccurrenceAt state) :
    Engine.ExactRootInquiryOccurrenceAt state.engine state.activation.query :=
  state.engine.ask state.activation

/-- Activate the inquiry compiler at this source-generated runtime state. -/
def State.tick
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    (state : runtime.State) : ExactActivatedInquiryOccurrenceAt state :=
  .mk

/-- Exact source-generated resolution. -/
def ExactActivatedInquiryOccurrenceAt.resolution
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :=
  activated.rawReadout.resolution

set_option linter.defProp false in
def ExactActivatedInquiryOccurrenceAt.resolution_eq_generated
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :=
  activated.rawReadout.resolution_eq_generated

/-- Answer and receipt are restrictions of the same sealed occurrence. -/
def ExactActivatedInquiryOccurrenceAt.answer
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :
    RootInquiryProcessNode.AnswerAt activated.resolution :=
  activated.rawReadout.answer

def ExactActivatedInquiryOccurrenceAt.receipt
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :
    RootInquiryProcessNode.ReceiptAt activated.resolution :=
  activated.rawReadout.receipt

/-- Generated macro successor of this exact inquiry. -/
def ExactActivatedInquiryOccurrenceAt.next
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) : Engine process :=
  activated.rawReadout.next

set_option linter.defProp false in
def ExactActivatedInquiryOccurrenceAt.next_erases_to_generated
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :=
  activated.rawReadout.next_erases_to_generated

set_option linter.defProp false in
def ExactActivatedInquiryOccurrenceAt.next_preservesGeneratedLivingLaw
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :=
  activated.rawReadout.next_preservesGeneratedLivingLaw

/-- Read the source compiler's already-generated inquiry resolution.  The
exact obstruction, failure, answer, receipt, and next remain in the dependent
`resolution`; this readout exposes only its outer constructor. -/
def ExactActivatedInquiryOccurrenceAt.resolutionKind
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :
    InquiryResolutionKind :=
  RootInquiryProcessNode.resolutionKind activated.resolution

/-- The next runtime state is generated by the exact inquiry target and the
recursive activation law. On U8 its engine is the revised living root. -/
def ExactActivatedInquiryOccurrenceAt.nextState
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) : runtime.State :=
  ⟨activated.next, runtime.activationLaw.nextAfter state.activation⟩

/-- Every token at the same runtime state is the canonical inquiry tick. -/
theorem ExactActivatedInquiryOccurrenceAt.eq_tick
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {state : runtime.State}
    (activated : ExactActivatedInquiryOccurrenceAt state) :
    activated = state.tick := by
  cases activated
  rfl

/-- Recursively generated runtime state after a finite number of inquiry
activations. No future state or query table is stored in the current atom. -/
def stateAt
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) : Nat → runtime.State
  | 0 => runtime.initialState
  | depth + 1 => (runtime.stateAt depth).tick.nextState

@[simp] theorem stateAt_zero
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) :
    runtime.stateAt 0 = runtime.initialState :=
  rfl

@[simp] theorem stateAt_succ
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) (depth : Nat) :
    runtime.stateAt (depth + 1) =
      (runtime.stateAt depth).tick.nextState :=
  rfl

@[simp] theorem stateAt_succ_engine
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) (depth : Nat) :
    (runtime.stateAt (depth + 1)).engine =
      (runtime.stateAt depth).tick.next :=
  rfl

@[simp] theorem stateAt_succ_activation
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) (depth : Nat) :
    (runtime.stateAt (depth + 1)).activation =
      runtime.activationLaw.nextAfter
        (runtime.stateAt depth).activation :=
  rfl

/-- Exact activated occurrence at one generated finite depth. -/
def tickAt
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) (depth : Nat) :
    ExactActivatedInquiryOccurrenceAt (runtime.stateAt depth) :=
  (runtime.stateAt depth).tick

/-! ## Repair-loop resumption

Certification is allowed to observe that a named runtime actually consumes
the repaired core.  It cannot construct a resolution or choose a branch: the
predicate below only eliminates the compiler-generated resolution already
stored in the exact tick. -/

/-- Exact dependent test that a generated resolution contains one fixed U8
core.  Direct, U7-settled and old-language answers cannot satisfy it. -/
def RootInquiryProcessNode.ResolutionAt.ContainsU8Core
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query)
    {Core : Type (u + 11)} (core : Core) : Prop :=
  match node with
  | .active _state =>
      match resolution with
      | .revised _obstruction _u7Gate _failure generated =>
          HEq generated core
      | .directlyAnswered ..
      | .u7Answered ..
      | .oldLanguageAnswered ..
      | .actualAction .. => False
  | .answered _state _priorQuery => nomatch query

/-- A generated inquiry resolution contains at most one U8 core. -/
theorem RootInquiryProcessNode.ResolutionAt.ContainsU8Core.core_heq
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    {resolution : node.ResolutionAt query}
    {CoreLeft : Type (u + 11)} {leftCore : CoreLeft}
    {CoreRight : Type (u + 11)} {rightCore : CoreRight}
    (left : RootInquiryProcessNode.ResolutionAt.ContainsU8Core
      resolution leftCore)
    (right : RootInquiryProcessNode.ResolutionAt.ContainsU8Core
      resolution rightCore) :
    HEq leftCore rightCore := by
  cases node with
  | active state =>
      cases resolution with
      | directlyAnswered answer consumer => exact False.elim left
      | u7Answered obstruction disposition answer => exact False.elim left
      | oldLanguageAnswered obstruction u7Gate answer consumer =>
          exact False.elim left
      | actualAction generated => exact False.elim left
      | revised obstruction u7Gate failure generated =>
          exact left.symm.trans right
  | answered state priorQuery => exact nomatch query

/-- The same named runtime has consumed the certified U8 core at this exact
finite depth.  Subsequent `tickAt` calls therefore resume from the core's
generated next rather than from a sibling compiler or a tooling receipt. -/
structure CofaceRealizationResumptionAt
    {Core : Type (u + 11)} (core : Core)
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process)
    (depth : Nat) : Prop where
  contains_core : RootInquiryProcessNode.ResolutionAt.ContainsU8Core
    (runtime.tickAt depth).resolution core

/-- One activated problem occurrence cannot consume two distinct U8 cores.
Copying or replaying the occurrence is only another read of the same compiler
image; a different core requires a newly generated problem occurrence. -/
theorem CofaceRealizationResumptionAt.core_heq
    {CoreLeft : Type (u + 11)} {leftCore : CoreLeft}
    {CoreRight : Type (u + 11)} {rightCore : CoreRight}
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {depth : Nat}
    (left : CofaceRealizationResumptionAt leftCore runtime depth)
    (right : CofaceRealizationResumptionAt rightCore runtime depth) :
    HEq leftCore rightCore :=
  RootInquiryProcessNode.ResolutionAt.ContainsU8Core.core_heq
    left.contains_core right.contains_core

/-- Exact dependent test that a named runtime resolution contains one fixed
sequential-action execution seal.  All ordinary and U8 branches are disjoint
from this authority. -/
def RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query)
    {Action : Type (u + 10)} (action : Action) : Prop :=
  match node with
  | .active _state =>
      match resolution with
      | .actualAction generated => HEq generated action
      | .directlyAnswered ..
      | .u7Answered ..
      | .oldLanguageAnswered ..
      | .revised .. => False
  | .answered _state _priorQuery => nomatch query

/-- One exact resolution cannot contain two distinct sequential actions. -/
theorem RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction.action_heq
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    {resolution : node.ResolutionAt query}
    {ActionLeft : Type (u + 10)} {leftAction : ActionLeft}
    {ActionRight : Type (u + 10)} {rightAction : ActionRight}
    (left : RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
      resolution leftAction)
    (right : RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
      resolution rightAction) :
    HEq leftAction rightAction := by
  cases node with
  | active state =>
      cases resolution with
      | directlyAnswered answer consumer => exact False.elim left
      | u7Answered obstruction disposition answer consumer =>
          exact False.elim left
      | oldLanguageAnswered obstruction u7Gate answer face consumer =>
          exact False.elim left
      | actualAction generated => exact left.symm.trans right
      | revised obstruction u7Gate failure generated =>
          exact False.elim left
  | answered state priorQuery => exact nomatch query

/-- The same named runtime consumed this exact sequential-action token at the
given depth.  The target remains a readout of the token's fixed program. -/
structure SequentialActualActionResumptionAt
    {Action : Type (u + 10)} (action : Action)
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process)
    (depth : Nat) : Prop where
  contains_action :
    RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
      (runtime.tickAt depth).resolution action

theorem SequentialActualActionResumptionAt.action_heq
    {ActionLeft : Type (u + 10)} {leftAction : ActionLeft}
    {ActionRight : Type (u + 10)} {rightAction : ActionRight}
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process}
    {depth : Nat}
    (left : SequentialActualActionResumptionAt leftAction runtime depth)
    (right : SequentialActualActionResumptionAt rightAction runtime depth) :
    HEq leftAction rightAction :=
  RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction.action_heq
    left.contains_action right.contains_action

/-- Complete, proposition-valued installation receipt for one strike output.

The candidate is the only post-frontier construction datum named by repair
tooling.  A concrete core and its dependent certification are existentially
sealed, while `CofaceRealizationResumptionAt` proves that this very core is the
    one consumed by the named runtime.  There is deliberately no independent
compiler witness: the actual runtime compiler is the installer. -/
def CofaceRealizationInstalledAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {oldTheory : TheoryState N}
    {Query : Type u} {query : Query}
    {InquiryEvent : Type (u + 1)} {event : InquiryEvent}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry}
    {obstruction : N.ObstructionAt
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {u7Gate : SourceNativeU7TheoryAuditAt calculus
      (calculus.generated obstruction).1}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (frontier : SourceNativeInquiryCofaceFrontierAt
      root visit U7 calculus oldTheory query event entry authority
        obstruction u7Gate failure)
    (candidate : SourceNativeInquiryCofaceRealizationAt frontier)
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process)
    (depth : Nat) : Prop :=
  ∃ (core : SourceGeneratedInquiryU8RevisionCoreAt
      root visit U7 calculus oldTheory query event entry authority
        obstruction u7Gate failure),
    SourceNativeInquiryCofaceRealizationCertificationAt candidate core ∧
      CofaceRealizationResumptionAt core runtime depth

/-- Finite observation of the exact inquiry process. Exhausting fuel is not
a terminal disposition; it only stops this readout. -/
inductive HistoryAt
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) :
    Nat → runtime.State → Type (u + 13)
  | exhausted (state : runtime.State) : HistoryAt runtime 0 state
  | step {fuel : Nat} {state : runtime.State}
      (activated : ExactActivatedInquiryOccurrenceAt state)
      (tail : HistoryAt runtime fuel activated.nextState) :
      HistoryAt runtime (fuel + 1) state

/-- Run exactly `fuel` canonical inquiry activations from one reachable
runtime state. -/
def runFrom
    {process : SourceNativeInquiryEngineProcess.{u}}
    {runtime : SourceNativeInquiryRuntime process} :
    (fuel : Nat) → (state : runtime.State) → HistoryAt runtime fuel state
  | 0, state => .exhausted state
  | fuel + 1, state =>
      let activated := state.tick
      .step activated (runFrom fuel activated.nextState)

/-- Finite observation from the source-generated initial runtime state. -/
def run
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) (fuel : Nat) :
    HistoryAt runtime fuel runtime.initialState :=
  runFrom fuel runtime.initialState

@[simp] theorem run_zero
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) :
    runtime.run 0 = .exhausted runtime.initialState :=
  rfl

@[simp] theorem run_succ
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process) (fuel : Nat) :
    runtime.run (fuel + 1) =
      .step runtime.initialState.tick
        (runFrom fuel runtime.initialState.tick.nextState) :=
  rfl

end SourceNativeInquiryRuntime

end RootInquiryCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
