import H0mework.Papers.SourceProcessCore
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
  let roots : List (String × String) := [("SaturationMonoid.ResponsibilityLifecycle.Regression.AdmissionEvent", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.Bearer", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.BoolLineageV", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.BoundaryEvent", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.Content", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.FixtureDebitEvent", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.Lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.P", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.ProtectedInterest", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.Scope", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.ScopeAnchorV", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.SourceEvent", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.TriggerState", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.V", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.acceptedAdmissionWitness", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.acceptedEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.acceptedFreshAllocation", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.acceptedPayload", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.acceptedPresent", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.acceptedSlot", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.acceptedState", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.accepted_progress_and_transfer_updates_one_exact_target", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.accepted_transfer_changes_bearer_preserves_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.actual_capacity_event_generates_obstruction", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.actual_lifecycle_run_is_budget_bounded", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.actual_maintenance_debit_preserves_anchor_and_incidence", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.boolLineageRestructuringVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.boolLineageVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.boundaryDisposition", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.capacityProcess", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.capacityVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.certifiedFullObserver", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.descendant_family_cannot_change_debt_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.descendant_family_cannot_launder_source_anchor_scope", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.emptyState", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.explicit_commitment_and_acceptance_admit", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.factoredFullObserver", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.factored_full_observer_commutes", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.firstMaintenanceDebit", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.firstMaintenanceDebitOwnership", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.fixtureDemand", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.fixtureObstruction", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.fixtureVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.full_observer_does_not_erase_source_anchor_scope", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.full_observer_is_consumer_safe", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.full_observer_sees_admission", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.incidenceLedger", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.incidence_ledger_has_no_phantom_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.inherited_origin_cannot_change_debt_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.inherited_origin_cannot_launder_source_anchor_scope", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.invisibleObserver", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.invisible_admission_is_hidden_not_safe", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.lifecycleBudgetAt", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.lifecycleBudgetProcess", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.lineageChildPayload", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.lineageParentPayload", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.maintainEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.maintainedPresent", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.maintainedSlot", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.mandatedEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.mandatedPayload", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.mandatedState", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.mergeReceipt", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.merge_cannot_change_debt_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.merge_cannot_launder_source_anchor_scope", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.merge_retains_each_local_criterion", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.next_actor_and_age_do_not_mutate_lifecycle", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.noAssumptionVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.noDeferReceiptIsEmpty", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.noDeferVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.obstruction_generates_demand_not_bearer_assignment", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.obstruction_only_does_not_admit", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.oneDebit", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.oneMaintenanceDebited", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.oneMaintenanceRun", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.process", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.progressTransferEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.renameReceipt", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.rename_does_not_reset_debt", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.reopenEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.reopenPayload", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.reopen_restores_live_same_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.restructuringVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.review_generates_typed_carry", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.scopeAnchorRestructuringVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.scopeAnchorVocabulary", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.scopeChildPayload", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.scopeChildState", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.scopeParentPayload", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.scopeParentState", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.secondMaintainEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.shortageReadout", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.shortage_generates_capacity_obstruction", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.splitReceipt", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.split_cannot_change_debt_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.split_cannot_launder_source_anchor_scope", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.split_retains_children_and_local_criteria", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.standing_mandate_override_admits", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.strictBudgetRun_arithmetic_bound", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.sufficientReadout", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.sufficient_capacity_generates_no_obstruction", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.supersedeEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.supersession_cannot_change_debt_lineage", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.supersession_keeps_live_successor", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminalArchive", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminalDisappears", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminalEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminalPresent", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminalReceiptWitness", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminalSlot", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminalState", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.terminal_exit_is_the_only_disappearance", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.threeDebits", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.transferEdge", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.transfer_offer_is_not_acceptance", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.triggerConsumer", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.triggerObserver", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.twoDebits", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.unclassifiedFixture", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.unclassified_does_not_default_safe", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.unreachableTriggerHiddenNull", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.unreachable_trigger_is_not_certified_safe", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.zeroDebits", "H0mework.Foundation.Responsibility.LifecycleRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.Regression.zero_budget_rejects_further_maintenance_debit", "H0mework.Foundation.Responsibility.LifecycleRegression")]
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
    ("token", toJson "e959e43a88bb20c910e0eff3779f0b6ffd72e86cb104d1d75719a8041e3788d9"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
