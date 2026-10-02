import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Birth
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Inventory
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Recognition
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-! Source-paid raw requests enter the existing inquiry runtime. Query
receipts stay on the first tick; equal complete inputs share future nodes. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request

open SourceOperationEffects DebtActivationWorld RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (inputs : old.Query → RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program)
variable (owners : (query : old.Query) → (inputs query).input.owner = old.entryAt query)
variable (payments : (query : old.Query) →
  GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
    (initialEvent (inputs query)).state)
variable (actions : (query : old.Query) → mathAction (initialEvent (inputs query)) = .inr (payments query))
variable (audits : (query : old.Query) → (old.compileInquiry query).audit = .answered)

inductive Stage : Type u
  | birth
  | math (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
      old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current) (depth : Nat)

def birthPresentation : RootInquiryStatePresentation where
  N := N
  V := V
  state := .create (birthState old program inputs scope owners)

def presentationAt : Stage (Value := Value) (Var := Var) (sort := sort) old → RootInquiryStatePresentation
  | .birth => birthPresentation old program inputs scope owners
  | .math registered depth => mathPresentation old program registered scope depth

private def erasedDepth (current : AnyAuthoritativeRootCurrent.{u}) : Option Nat :=
  match current.current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem finiteDepth (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current) (count : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit old program registered scope count).history = count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit old program registered scope count).history + 1 = count + 1
      rw [previous]

theorem presentationAt_erase_injective : Function.Injective
    (fun stage => (presentationAt old program inputs scope owners stage).erase) := by
  intro first second same
  cases first with
  | birth =>
      cases second with
      | birth => rfl
      | math registered depth =>
          exact False.elim ((Inventory.birth_math_erasure_ne old program registered scope (depth + 1)) same)
  | math first firstDepth =>
      cases second with
      | birth =>
          exact False.elim ((Inventory.birth_math_erasure_ne old program first scope (firstDepth + 1)) same.symm)
      | math second secondDepth =>
          have registered := registered_eq_of_erasure old program scope first second
            (mathVisit old program first scope firstDepth) (mathVisit old program second scope secondDepth) same
          subst second
          have firstRead : erasedDepth (mathPresentation old program first scope firstDepth).erase =
              some (firstDepth + 1) := congrArg some (finiteDepth old program scope first (firstDepth + 1))
          have secondRead : erasedDepth (mathPresentation old program first scope secondDepth).erase =
              some (secondDepth + 1) := congrArg some (finiteDepth old program scope first (secondDepth + 1))
          have depths := congrArg erasedDepth same
          change erasedDepth (mathPresentation old program first scope firstDepth).erase =
            erasedDepth (mathPresentation old program first scope secondDepth).erase at depths
          rw [firstRead, secondRead] at depths
          exact congrArg (Stage.math first) (Nat.add_right_cancel (Option.some.inj depths))

def generated (query : old.Query) :=
  (birthProgramAt old program inputs scope owners query (payments query) (actions query)).generate
    (old.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt old.visit)

include audits in
theorem birth_compiles (query : old.Query) :
    (birthState old program inputs scope owners).compileInquiry query =
      .debtAdmission (generated old program inputs scope owners payments actions query) :=
  compilationAt_paid old program inputs scope owners query (payments query) (audits query) (actions query) _

set_option linter.defProp false in
def birth_successor (query : old.Query) := RootInquiryProcessNode.active_debtAdmission_successor_valid
  (birthPresentation old program inputs scope owners) (mathPresentation old program (inputs query) scope 0)
  query (generated old program inputs scope owners payments actions query)
  (birth_compiles old program inputs scope owners payments actions audits query)
  (birthProgramAt_next old program inputs scope owners query (payments query) (actions query) _).symm
  (birthProgramAt_root old program inputs scope owners query (payments query) (actions query) _).symm

set_option linter.defProp false in
def math_successor (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current) (depth : Nat) :=
  RootInquiryProcessNode.active_directlyAnswered_successor_valid
    (mathPresentation old program registered scope depth) (mathPresentation old program registered scope (depth + 1))
    PUnit.unit (mathAnswerFace old program registered scope depth) (mathConsumer old program registered scope depth)
    (math_compiles old program registered scope depth)
    (by
      apply congrArg (fun current => (⟨NewN old registered, current⟩ : AnyAuthoritativeRootCurrent.{u}))
      symm
      apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
      rfl) HEq.rfl

def inquiryProcess : SourceNativeInquiryEngineProcess.{u} where
  State := Stage (Value := Value) (Var := Var) (sort := sort) old
  stateAt := fun stage => .active (presentationAt old program inputs scope owners stage)
  erase_injective := by
    intro first second firstState secondState firstActive secondActive same
    cases firstActive
    cases secondActive
    exact presentationAt_erase_injective old program inputs scope owners same
  initial := .birth
  successorAt := by
    intro stage query
    cases stage with
    | birth => exact ⟨.math (inputs query) 0, birth_successor old program inputs scope owners payments actions audits query⟩
    | math registered depth =>
        cases query
        exact ⟨.math registered (depth + 1), math_successor old program scope registered depth⟩

variable [Unique old.Query]

def initialQuery : ((inquiryProcess old program inputs scope owners payments actions audits).stateAt
    (inquiryProcess old program inputs scope owners payments actions audits).initial).Query := (default : old.Query)

omit [Unique old.Query] in
def nextQueryAt (stage : Stage (Value := Value) (Var := Var) (sort := sort) old)
    (query : ((inquiryProcess old program inputs scope owners payments actions audits).stateAt stage).Query) :
    ((inquiryProcess old program inputs scope owners payments actions audits).stateAt
      ((inquiryProcess old program inputs scope owners payments actions audits).successorAt stage query).1).Query := by
  cases stage with
  | birth => exact PUnit.unit
  | math registered depth => cases query; exact PUnit.unit

omit [Unique old.Query] in
theorem nextQuery_unique (stage : Stage (Value := Value) (Var := Var) (sort := sort) old)
    (query : ((inquiryProcess old program inputs scope owners payments actions audits).stateAt stage).Query)
    (candidate : ((inquiryProcess old program inputs scope owners payments actions audits).stateAt
      ((inquiryProcess old program inputs scope owners payments actions audits).successorAt stage query).1).Query) :
    candidate = nextQueryAt old program inputs scope owners payments actions audits stage query := by
  cases stage with
  | birth => cases candidate; rfl
  | math registered depth => cases query; cases candidate; rfl

def inquiryRuntime : SourceNativeInquiryRuntime (inquiryProcess old program inputs scope owners payments actions audits) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    (initialQuery old program inputs scope owners payments actions audits)
    (fun candidate => by
      change candidate = (default : old.Query)
      exact Subsingleton.elim (α := old.Query) candidate (default : old.Query))
    (nextQueryAt old program inputs scope owners payments actions audits)
    (nextQuery_unique old program inputs scope owners payments actions audits)

omit [Unique old.Query] in
def inquiryRuntimeRegistered
    (input : Engine.SourceNativeInquiryRegisteredInputAt
      (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits))) :
    SourceNativeInquiryRuntime (inquiryProcess old program inputs scope owners payments actions audits) where
  activationLaw :=
    { initial := (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits)).registeredInquiryActivation input
      nextAt := fun stage activation =>
        Engine.uniqueInquiryActivation _
            (nextQueryAt old program inputs scope owners payments actions audits stage activation.query)
            (nextQuery_unique old program inputs scope owners payments actions audits stage activation.query) }

omit [Unique old.Query] in
theorem registered_initial_query
    (input : Engine.SourceNativeInquiryRegisteredInputAt
      (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits))) :
    (inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).initialState.activation.query =
      input.query := rfl

omit [Unique old.Query] in
theorem registered_initial_origin
    (input : Engine.SourceNativeInquiryRegisteredInputAt
      (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits))) :
    (inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).initialState.activation.origin =
      .registered input := rfl

def firstTick := (inquiryRuntime old program inputs scope owners payments actions audits).tickAt 0

theorem initial_resolution : (firstTick old program inputs scope owners payments actions audits).resolution =
    .debtAdmission (generated old program inputs scope owners payments actions default) := by
  exact RootInquiryProcessNode.active_debtAdmission_resolution_eq
    (birthPresentation old program inputs scope owners) (default : old.Query)
    (generated old program inputs scope owners payments actions default)
    (birth_compiles old program inputs scope owners payments actions audits (default : old.Query))

theorem initial_resolution_kind : (firstTick old program inputs scope owners payments actions audits).resolutionKind =
    .debtAdmission := by
  rw [SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.resolutionKind,
    initial_resolution old program inputs scope owners payments actions audits]
  rfl

omit [Unique old.Query] in
private theorem next_node_math (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current) (depth : Nat)
    (engine : Engine (inquiryProcess old program inputs scope owners payments actions audits))
    (same : engine.node = .active (mathPresentation old program registered scope depth))
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (engine.ask activation).next.node = .active (mathPresentation old program registered scope (depth + 1)) := by
  rcases engine with ⟨stage⟩
  have presentations : presentationAt old program inputs scope owners stage =
      mathPresentation old program registered scope depth := RootInquiryProcessNode.active.inj same
  have stageEq : stage = .math registered depth := presentationAt_erase_injective old program inputs scope owners
    (congrArg RootInquiryStatePresentation.erase presentations)
  subst stage
  rcases activation with ⟨query⟩
  cases query
  rfl

theorem stateAt_afterBirth_node (depth : Nat) :
    ((inquiryRuntime old program inputs scope owners payments actions audits).stateAt (depth + 1)).engine.node =
      .active (mathPresentation old program (inputs default) scope depth) := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
      exact next_node_math old program inputs scope owners payments actions audits (inputs default) depth
        ((inquiryRuntime old program inputs scope owners payments actions audits).stateAt (depth + 1)).engine previous
        ((inquiryRuntime old program inputs scope owners payments actions audits).stateAt (depth + 1)).activation

omit [Unique old.Query] in
theorem registered_stateAt_afterBirth_node
    (input : Engine.SourceNativeInquiryRegisteredInputAt
      (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits))) (depth : Nat) :
    ((inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).stateAt (depth + 1)).engine.node =
      .active (mathPresentation old program (inputs input.query) scope depth) := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
      exact next_node_math old program inputs scope owners payments actions audits (inputs input.query) depth
        ((inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).stateAt (depth + 1)).engine previous
        ((inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).stateAt (depth + 1)).activation

theorem bornResumption : SourceNativeInquiryRuntime.DebtAdmissionActualActionResumptionAt
    (generated old program inputs scope owners payments actions default)
    (inquiryRuntime old program inputs scope owners payments actions audits) 0 where
  contains_action := by rw [initial_resolution old program inputs scope owners payments actions audits]; exact HEq.rfl

omit [Unique old.Query] in
def registeredFirstTick
    (input : Engine.SourceNativeInquiryRegisteredInputAt
      (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits))) :=
  (inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).tickAt 0

omit [Unique old.Query] in
theorem registered_initial_resolution
    (input : Engine.SourceNativeInquiryRegisteredInputAt
      (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits))) :
    (registeredFirstTick old program inputs scope owners payments actions audits input).resolution =
      .debtAdmission (generated old program inputs scope owners payments actions input.query) := by
  exact RootInquiryProcessNode.active_debtAdmission_resolution_eq
    (birthPresentation old program inputs scope owners) input.query
    (generated old program inputs scope owners payments actions input.query)
    (birth_compiles old program inputs scope owners payments actions audits input.query)

omit [Unique old.Query] in
theorem registeredBornResumption
    (input : Engine.SourceNativeInquiryRegisteredInputAt
      (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits))) :
    SourceNativeInquiryRuntime.DebtAdmissionActualActionResumptionAt
      (generated old program inputs scope owners payments actions input.query)
      (inquiryRuntimeRegistered old program inputs scope owners payments actions audits input) 0 where
  contains_action := by
    rw [registered_initial_resolution old program inputs scope owners payments actions audits input]
    exact HEq.rfl

end
end RootGeneratedDebtActivationJointSource.Native.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
