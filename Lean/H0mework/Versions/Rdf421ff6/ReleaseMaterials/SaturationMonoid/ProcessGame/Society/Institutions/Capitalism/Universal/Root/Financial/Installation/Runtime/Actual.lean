import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Registry

/-! Canonical activated ticks consume the source-selected core.  The first
two ticks are the registered programme and its accounting ingress; every
later tick remains active on the exact generated financial root. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open SourceNativeInquiryRuntime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (positive : 0 < ProgrammeSource.registrationSize input)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)
  (initialZero : input.initial.claims = fun _ _ _ => 0)

def originalInputCore := InputSource.core (datum input) oldVisit sourceIndex boundary
  (inputQuery input oldVisit sourceIndex boundary)

theorem actual_registered_core_is_consumed : CofaceRealizationResumptionAt
    (originalInputCore input oldVisit sourceIndex boundary)
    (runtime input positive oldVisit sourceIndex boundary initialZero) 0 := ⟨HEq.rfl⟩

theorem actual_registered_core_is_unique {Core : Type 11} {candidate : Core}
    (consumed : CofaceRealizationResumptionAt candidate
      (runtime input positive oldVisit sourceIndex boundary initialZero) 0) :
    HEq candidate (originalInputCore input oldVisit sourceIndex boundary) :=
  consumed.core_heq (actual_registered_core_is_consumed input positive oldVisit sourceIndex boundary initialZero)

theorem actual_ingress_is_consumed : SequentialActualActionResumptionAt
    (Ingress.generated input 1) (runtime input positive oldVisit sourceIndex boundary initialZero) 1 := ⟨HEq.rfl⟩

theorem actual_ingress_is_unique {Action : Type 10} {candidate : Action}
    (consumed : SequentialActualActionResumptionAt candidate
      (runtime input positive oldVisit sourceIndex boundary initialZero) 1) :
    HEq candidate (Ingress.generated input 1) :=
  consumed.action_heq (actual_ingress_is_consumed input positive oldVisit sourceIndex boundary initialZero)

private theorem next_account_node (count : Nat)
    (engine : Engine (process input positive oldVisit sourceIndex boundary))
    (same : engine.node = .active ((frames input 1 count).presentation input))
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (engine.ask activation).next.node = .active ((frames input 1 (count + 1)).presentation input) := by
  rcases engine with ⟨stage⟩
  have exactStage : stage = Stage.account count :=
    (process input positive oldVisit sourceIndex boundary).erase_injective rfl rfl
      (congrArg RootInquiryProcessNode.erase same)
  subst stage
  rfl

theorem actual_account_node (count : Nat) :
    ((runtime input positive oldVisit sourceIndex boundary initialZero).stateAt (count + 2)).engine.node =
      .active ((frames input 1 count).presentation input) := by
  induction count with
  | zero => rfl
  | succ count prior =>
      exact next_account_node input positive oldVisit sourceIndex boundary count
        ((runtime input positive oldVisit sourceIndex boundary initialZero).stateAt (count + 2)).engine prior
        ((runtime input positive oldVisit sourceIndex boundary initialZero).stateAt (count + 2)).activation

theorem actual_account_next (count : Nat) :
    ((runtime input positive oldVisit sourceIndex boundary initialZero).tickAt (count + 2)).next.node =
      .active ((frames input 1 (count + 1)).presentation input) :=
  actual_account_node input positive oldVisit sourceIndex boundary initialZero (count + 1)

private theorem debt_action_on_exact_engine (count : Nat)
    (engine : Engine (process input positive oldVisit sourceIndex boundary))
    (same : engine.node = .active ((frames input 1 count).presentation input))
    (activation : Engine.SourceNativeInquiryActivationAt engine)
    (registered : Registration input (frames input 1 count).native (frames input 1 count).visit.current)
    (selected : registration? input (frames input 1 count).native (frames input 1 count).visit.current = some registered) :
    RootInquiryProcessNode.ResolutionAt.ContainsDebtAdmissionActualAction (engine.ask activation).resolution
      (debtCore input (frames input 1 count).native ((frames input 1 count).temporal input)
        (frames input 1 count).authority registered) := by
  have emitted := (engine.ask activation).resolution_eq_generated
  rcases engine with ⟨stage⟩
  have exactStage : stage = Stage.account count :=
    (process input positive oldVisit sourceIndex boundary).erase_injective rfl rfl
      (congrArg RootInquiryProcessNode.erase same)
  subst stage
  have compiled : ((frames input 1 count).presentation input).state.base.compileInquiry activation.query =
      .debtAdmission (debtCore input (frames input 1 count).native ((frames input 1 count).temporal input)
        (frames input 1 count).authority registered) := by
    have queryEq := (frames input 1 count).query_unique input activation.query
    rw [queryEq]
    exact source_selected_debt_core input (frames input 1 count).native (frames input 1 count).installed
      ((frames input 1 count).temporal input) (frames input 1 count).authority registered selected
  have resolved := RootInquiryProcessNode.active_debtAdmission_resolution_eq
    ((frames input 1 count).presentation input) activation.query
    (debtCore input (frames input 1 count).native ((frames input 1 count).temporal input)
      (frames input 1 count).authority registered) compiled
  have wholeResolution := emitted.trans resolved
  rw [wholeResolution]
  exact HEq.rfl

theorem actual_debt_core_is_consumed (count : Nat)
    (registered : Registration input (frames input 1 count).native (frames input 1 count).visit.current)
    (selected : registration? input (frames input 1 count).native (frames input 1 count).visit.current = some registered) :
    DebtAdmissionActualActionResumptionAt
      (debtCore input (frames input 1 count).native ((frames input 1 count).temporal input)
        (frames input 1 count).authority registered)
      (runtime input positive oldVisit sourceIndex boundary initialZero) (count + 2) :=
  ⟨debt_action_on_exact_engine input positive oldVisit sourceIndex boundary count
    ((runtime input positive oldVisit sourceIndex boundary initialZero).stateAt (count + 2)).engine
    (actual_account_node input positive oldVisit sourceIndex boundary initialZero count)
    ((runtime input positive oldVisit sourceIndex boundary initialZero).stateAt (count + 2)).activation
    registered selected⟩

private theorem debt_contains_unique {node : RootInquiryProcessNode} {query : node.Query}
    (resolution : node.ResolutionAt query) {A B : Type 10} {left : A} {right : B}
    (first : RootInquiryProcessNode.ResolutionAt.ContainsDebtAdmissionActualAction resolution left)
    (second : RootInquiryProcessNode.ResolutionAt.ContainsDebtAdmissionActualAction resolution right) :
    HEq left right := by
  cases node with
  | answered _ _ => exact nomatch query
  | active source =>
      cases resolution with
      | debtAdmission actual => exact first.symm.trans second
      | directlyAnswered _ _ => exact False.elim first
      | u7Answered _ _ _ _ => exact False.elim first
      | oldLanguageAnswered _ _ _ _ _ => exact False.elim first
      | actualAction _ => exact False.elim first
      | revised _ _ _ _ => exact False.elim first

theorem actual_debt_core_is_unique (count : Nat)
    (registered : Registration input (frames input 1 count).native (frames input 1 count).visit.current)
    (selected : registration? input (frames input 1 count).native (frames input 1 count).visit.current = some registered)
    {Action : Type 10} {candidate : Action}
    (consumed : DebtAdmissionActualActionResumptionAt candidate
      (runtime input positive oldVisit sourceIndex boundary initialZero) (count + 2)) :
    HEq candidate (debtCore input (frames input 1 count).native ((frames input 1 count).temporal input)
      (frames input 1 count).authority registered) :=
  debt_contains_unique _ consumed.contains_action
    (actual_debt_core_is_consumed input positive oldVisit sourceIndex boundary initialZero count
      registered selected).contains_action

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
