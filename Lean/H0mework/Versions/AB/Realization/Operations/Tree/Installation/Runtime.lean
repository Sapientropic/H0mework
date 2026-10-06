import H0mework.Versions.AB.Realization.Operations.Tree.Installation.FockSource
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Runtime

/-! The existing registered-request runtime consumes the generated source
input and actual first step. Source syntax pays through the original whole
rows and produces its own canonical mathematical continuation. -/

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Installation.Fock
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
namespace G
export RootGeneratedDebtActivationJointSource
  (RegisteredAt RawInputAt register initialEvent mathAction)
namespace R
export RootGeneratedDebtActivationJointSource.Native.Request
  (inquiryProcess inquiryRuntimeRegistered registered_initial_query registered_initial_origin
   registered_stateAt_afterBirth_node registeredBornResumption)
end R
end G
variable (runtime : LivingRuntimeState process) (depth : Nat)

abbrev old := queryState runtime depth

def registered (candidate : (old runtime depth).Query) :
    G.RegisteredAt (Value := Value) (Var := Var) (sort := .result)
      (old runtime depth).root.toAuthoritativeRoot.toLedgerRoot (old runtime depth).visit.current :=
  G.register fun occurrence => by
    rcases occurrence with ⟨support, event⟩
    cases event
    exact { environment := environment
            expression := program (actualTree runtime depth)
            owner := (old runtime depth).entryAt candidate }

def inputs (candidate : (old runtime depth).Query) := registered runtime depth candidate

theorem owners (candidate : (old runtime depth).Query) :
    (inputs runtime depth candidate).input.owner = (old runtime depth).entryAt candidate := rfl

private theorem not_settled (candidate : (old runtime depth).Query)
    (settled : SourceOperationExecutionDebt.Settlement (G.initialEvent (inputs runtime depth candidate)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.law (inputs runtime depth candidate)).settlement_budget_zero settled
  change remaining (program (actualTree runtime depth)) = 0 at zero
  rw [program_budget] at zero
  have positive : 0 < budget (actualTree runtime depth) := by
    cases actualTree runtime depth with
    | occur origin branches =>
        change 0 < 1 + branchWork branches
        omega
  omega

def payments (candidate : (old runtime depth).Query) :
    GeneratedStepAt (RootGeneratedDebtActivationJointSource.Idle.law
      (inputs runtime depth candidate).input.environment (inputs runtime depth candidate).input.expression)
      (G.initialEvent (inputs runtime depth candidate)).state :=
  match G.mathAction (G.initialEvent (inputs runtime depth candidate)) with
  | .inl settled => False.elim (not_settled runtime depth candidate settled)
  | .inr paid => paid

theorem actions (candidate : (old runtime depth).Query) :
    G.mathAction (G.initialEvent (inputs runtime depth candidate)) = .inr (payments runtime depth candidate) := by
  cases selected : G.mathAction (G.initialEvent (inputs runtime depth candidate)) with
  | inl settled => exact False.elim (not_settled runtime depth candidate settled)
  | inr paid => simp only [payments, selected]

theorem audits (candidate : (old runtime depth).Query) :
    ((old runtime depth).compileInquiry candidate).audit = .answered := rfl

abbrev registeredProcess := G.R.inquiryProcess (old runtime depth) (nativeProgram runtime depth)
  (inputs runtime depth) (nativeScope runtime depth) (owners runtime depth)
  (payments runtime depth) (actions runtime depth) (audits runtime depth)

def actualInput : Engine.SourceNativeInquiryRegisteredInputAt (Engine.initial (registeredProcess runtime depth)) :=
  queryInput (state runtime depth) (treeSource runtime depth) (incidence runtime depth)

def inquiry := G.R.inquiryRuntimeRegistered (old runtime depth) (nativeProgram runtime depth)
  (inputs runtime depth) (nativeScope runtime depth) (owners runtime depth)
  (payments runtime depth) (actions runtime depth) (audits runtime depth) (actualInput runtime depth)

theorem actual_query : (inquiry runtime depth).initialState.activation.query =
    (actualInput runtime depth).query := rfl

theorem actual_origin : (inquiry runtime depth).initialState.activation.origin =
    .registered (actualInput runtime depth) := rfl

theorem actual_math_node (count : Nat) :
    ((inquiry runtime depth).stateAt (count + 1)).engine.node =
      .active (RootGeneratedDebtActivationJointSource.Native.Request.mathPresentation
        (old runtime depth) (nativeProgram runtime depth)
        (inputs runtime depth (actualInput runtime depth).query) (nativeScope runtime depth) count) :=
  G.R.registered_stateAt_afterBirth_node (old runtime depth) (nativeProgram runtime depth)
    (inputs runtime depth) (nativeScope runtime depth) (owners runtime depth)
    (payments runtime depth) (actions runtime depth) (audits runtime depth) (actualInput runtime depth) count

theorem actual_birth : type_of% (G.R.registeredBornResumption (old runtime depth) (nativeProgram runtime depth)
  (inputs runtime depth) (nativeScope runtime depth) (owners runtime depth)
  (payments runtime depth) (actions runtime depth) (audits runtime depth) (actualInput runtime depth)) := G.R.registeredBornResumption (old runtime depth) (nativeProgram runtime depth)
  (inputs runtime depth) (nativeScope runtime depth) (owners runtime depth)
  (payments runtime depth) (actions runtime depth) (audits runtime depth) (actualInput runtime depth)

end SourceOperationNative.Tree.Installation.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
