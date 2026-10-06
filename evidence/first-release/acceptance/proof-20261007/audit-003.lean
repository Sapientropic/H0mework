import H0mework.Papers.SourceProcessCoreAb
import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet ++ info.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := [("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Idle.identityTransport", "H0mework.Foundation.Responsibility.JointSource.Idle"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Idle.law", "H0mework.Foundation.Responsibility.JointSource.Idle"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Idle.transportLaw", "H0mework.Foundation.Responsibility.JointSource.Idle"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Idle.wholeEvolution", "H0mework.Foundation.Responsibility.JointSource.Idle"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.action_is_paid", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression_eval", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.old_value", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_value", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_zero_iff", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value", "H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.Action", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.Occurrence", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.action", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.activeEnvironment", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.actual_paid_receipt", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.birth_compiles", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.born", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.currentPresentation", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.currentState", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.environmentAt", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.event", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.firstStep", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.material", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.no_paid_of_zero", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.observation_source", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Inventory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.paidRead", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.paid_action", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.paid_state", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.rank_eq_of_erasure", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Inventory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.rawFace", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.rawRead", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.raw_environment", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.raw_eq_of_erasure", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Inventory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.raw_expression", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.request", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.request_effect", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Residual"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.request_inverse_fibre", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Residual"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Frame.successor_valid", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Occurrence"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.actual_node", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.frames", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.frames_erase_injective", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Inventory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.inquiryProcess", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.macro_next", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.macro_next_preserves", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.observation", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Inventory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.runtime", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.runtime_debt_current_actual", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.LocalOperationAt", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.completed", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.completed_history", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.completed_value", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.frontier", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.normal", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.realization", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.seed", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.sourceFace", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.sourceRead", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.source_payload", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.targetRuntime", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_depth", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_factorizes", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_state", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Calculation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Completion.budget", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Completion.completed_history_length", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Completion.completed_next_state", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Completion.completed_value", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.original_material", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_boundary", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.updated_inverse_fibre", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Payment.debtCurrent", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Payment.debtStep", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Payment.endpoint_no_paid", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Payment.no_refill", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Payment.wellFounded", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Payment"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Authority"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.compiler", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.destination_math", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.eventAlgebra", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.ledgerRoot", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.mathEntry", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.patch", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.patch_fold", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.process", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.remainder", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.tick_math", "H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.vocabulary", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.wholeOf", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.Advance", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.Settlement", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.State", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.advance", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.completed_value", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.generate", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.initial", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.law", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Installation.generatedInquiry", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Installation.material_generated", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Installation.old_compilation_preserved", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Installation.query_tree", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Installation.result_tree", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.actual_effect_charge", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.actual_effect_value", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.generatedFeed", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.nativePacket", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.original_whole_next", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.sourceFeed", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.Occurrence", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.TreeReadAt", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.actual_budget", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.actual_trace", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.actual_value", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.answer_next", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.completed_cost", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.query_charged_history", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.query_original_material", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.reader", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Installation.treeAt", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Installation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Inverse.Mother.query_tree", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Recovery"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Inverse.Mother.recovered_tree", "H0mework.Versions.AB.Realization.Operations.Tree.Fold.Recovery"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Inverse.program_injective", "H0mework.Realization.Operations.Tree.Fold.Inverse"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Inverse.read_program", "H0mework.Realization.Operations.Tree.Fold.Inverse"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.program", "H0mework.Realization.Operations.Tree.Fold.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.program_budget", "H0mework.Realization.Operations.Tree.Fold.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.program_value", "H0mework.Realization.Operations.Tree.Fold.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.source_boundary", "H0mework.Realization.Operations.Tree.Fold.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.trace_budget", "H0mework.Realization.Operations.Tree.Fold.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.actualRegistered", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.actual_budget", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.actual_next", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.completed", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.completed_cost", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.completed_original_write", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.completed_physical_source", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.completed_value", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.generatedPayment", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.macro_next", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.registered_environment", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.registered_expression", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.same_debt_wellFounded", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.strictPayment", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Installation.Fock.wholeReceipt", "H0mework.Versions.AB.Realization.Operations.Tree.Installation.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Program", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Value", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Var", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.appendBranches", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.appendConstructor", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.appendTree", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.appendUnits", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.branchWork", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.budget", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.environment", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.program", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.program_budget", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.program_source", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.sourceTrace", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.trace_charged", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.unitWork", "H0mework.Versions.AB.Realization.Operations.Tree.Source"),
    ("SaturationMonoid.SourceOperationExecution.Step", "H0mework.Realization.Operations.Execution.Step"),
    ("SaturationMonoid.SourceOperationExecution.Step.relationWords", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Step.relation_boundary", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Step.remaining_eq", "H0mework.Realization.Operations.Execution.Step"),
    ("SaturationMonoid.SourceOperationExecution.Step.sound", "H0mework.Realization.Operations.Execution.Step"),
    ("SaturationMonoid.SourceOperationExecution.Step.toDerivation", "H0mework.Realization.Operations.Execution.Step"),
    ("SaturationMonoid.SourceOperationExecution.Trace", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.addLeft", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.addRight", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.append", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.bilinearLeft", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.bilinearRight", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.length", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.length_to_const", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.linear", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relationWords", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relationWords_append", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_boundary", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_cochain", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_inventory", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_old", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.remaining_eq", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.single", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.sound", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.toDerivation", "H0mework.Realization.Operations.Execution.Trace"),
    ("SaturationMonoid.SourceOperationExecution.Trace.updated_residual", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.updated_zero_iff", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.completed_trace_value", "H0mework.Realization.Operations.Execution.Run"),
    ("SaturationMonoid.SourceOperationExecution.const_no_step", "H0mework.Realization.Operations.Execution.Step"),
    ("SaturationMonoid.SourceOperationExecution.execution", "H0mework.Realization.Operations.Execution.Run"),
    ("SaturationMonoid.SourceOperationExecution.execution_length", "H0mework.Realization.Operations.Execution.Run"),
    ("SaturationMonoid.SourceOperationExecution.remaining", "H0mework.Realization.Operations.Execution.Step"),
    ("SaturationMonoid.SourceOperationExecution.step_wellFounded", "H0mework.Realization.Operations.Execution.Step")]
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let closure := recoveryClosure env (roots.map fun item => releaseName item.1)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "298aa6040fcbd9a0fd7ba9df2d83497b8c7c44d8173c649ad032a18c5b4553cc"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
