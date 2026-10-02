import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Residual.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Runtime

/-! The same current emits another actual debt admission. All old rows and
installed source faces travel through the existing complete-native producer. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Residual

open SourceOperationEffects SourceOperationExecution DebtActivationWorld RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program) (depth : Nat)
variable (environmentAt : Occurrence old program registered scope depth → Env Value Var)

def inputs (_query : (currentState old program registered scope depth).Query) :=
  nextRegistered old program registered scope depth environmentAt

theorem owners (query : (currentState old program registered scope depth).Query) :
    (inputs old program registered scope depth environmentAt query).input.owner =
      (currentState old program registered scope depth).entryAt query := by
  cases query
  rfl

private theorem notSettled (settled : SourceOperationExecutionDebt.Settlement
    (initialEvent (nextRegistered old program registered scope depth environmentAt)).state) : False := by
  have zero := (law (nextRegistered old program registered scope depth environmentAt)).settlement_budget_zero settled
  have positive := budget old program registered scope depth environmentAt
  change remaining (nextRegistered old program registered scope depth environmentAt).input.expression = 0 at zero
  omega

def firstStep : GeneratedStepAt (law (nextRegistered old program registered scope depth environmentAt))
    (initialEvent (nextRegistered old program registered scope depth environmentAt)).state :=
  match mathAction (initialEvent (nextRegistered old program registered scope depth environmentAt)) with
  | .inl settled => False.elim (notSettled old program registered scope depth environmentAt settled)
  | .inr paid => paid

theorem firstStep_generated : mathAction
    (initialEvent (nextRegistered old program registered scope depth environmentAt)) =
      .inr (firstStep old program registered scope depth environmentAt) := by
  cases selected : mathAction (initialEvent (nextRegistered old program registered scope depth environmentAt)) with
  | inl settled => exact False.elim (notSettled old program registered scope depth environmentAt settled)
  | inr paid => simp only [firstStep, selected]

def payments (query : (currentState old program registered scope depth).Query) := by
  cases query
  exact firstStep old program registered scope depth environmentAt

theorem actions (query : (currentState old program registered scope depth).Query) :
    mathAction (initialEvent (inputs old program registered scope depth environmentAt query)) =
      .inr (payments old program registered scope depth environmentAt query) := by
  cases query
  exact firstStep_generated old program registered scope depth environmentAt

theorem audits (query : (currentState old program registered scope depth).Query) :
    ((currentState old program registered scope depth).compileInquiry query).audit = .answered := by
  cases query
  rfl

local instance : Unique (currentState old program registered scope depth).Query := (inferInstance : Unique PUnit)

def inquiry := inquiryRuntime
  (currentState old program registered scope depth) (nextProgram old program registered scope)
  (inputs old program registered scope depth environmentAt) (nextScope old program registered scope)
  (owners old program registered scope depth environmentAt)
  (payments old program registered scope depth environmentAt)
  (actions old program registered scope depth environmentAt) (audits old program registered scope depth)

theorem initial_kind : ((inquiry old program registered scope depth environmentAt).tickAt 0).resolutionKind =
    .debtAdmission := initial_resolution_kind
  (currentState old program registered scope depth) (nextProgram old program registered scope)
  (inputs old program registered scope depth environmentAt) (nextScope old program registered scope)
  (owners old program registered scope depth environmentAt)
  (payments old program registered scope depth environmentAt)
  (actions old program registered scope depth environmentAt) (audits old program registered scope depth)

theorem actual_node (count : Nat) :
    ((inquiry old program registered scope depth environmentAt).stateAt (count + 1)).engine.node =
      .active (mathPresentation (currentState old program registered scope depth)
        (nextProgram old program registered scope) (nextRegistered old program registered scope depth environmentAt)
        (nextScope old program registered scope) count) :=
  stateAt_afterBirth_node
    (currentState old program registered scope depth) (nextProgram old program registered scope)
    (inputs old program registered scope depth environmentAt) (nextScope old program registered scope)
    (owners old program registered scope depth environmentAt)
    (payments old program registered scope depth environmentAt)
    (actions old program registered scope depth environmentAt) (audits old program registered scope depth) count

def completed := Completion.completed
  (currentState old program registered scope depth) (nextProgram old program registered scope)
  (nextRegistered old program registered scope depth environmentAt) (nextScope old program registered scope)

theorem completed_value : (completed old program registered scope depth environmentAt).1 =
    (nextRegistered old program registered scope depth environmentAt).input.expression.eval
      (nextRegistered old program registered scope depth environmentAt).input.environment :=
  Completion.completed_value
    (currentState old program registered scope depth) (nextProgram old program registered scope)
    (nextRegistered old program registered scope depth environmentAt) (nextScope old program registered scope)

end
end RootGeneratedDebtActivationJointSource.Native.Request.Residual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
