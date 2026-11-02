import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Input.Process

/-! The registered full-input receipt activates the original inquiry.  Its
actual tick consumes the computed core; subsequent activations arise only
from that tick's generated target on the same revised living root. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (datum : Datum Party Good Port Technology Instrument)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

@[simp] theorem source_successor (query : Query datum oldVisit sourceIndex boundary) :
    ((process datum oldVisit sourceIndex boundary).successorAt .source query).val =
      RegistryState.target 2 := by
  have unique := germ_unique datum _ query
  cases unique
  rfl

@[simp] theorem target_successor (index : Nat)
    (query : ((process datum oldVisit sourceIndex boundary).stateAt (.target index)).Query) :
    ((process datum oldVisit sourceIndex boundary).successorAt (.target index) query).val =
      RegistryState.target (index + 1) := rfl

def initialInput : Engine.SourceNativeInquiryRegisteredInputAt
    (Engine.initial (process datum oldVisit sourceIndex boundary)) :=
  registeredInput datum (visit datum oldVisit sourceIndex boundary)

def nextQuery (state : RegistryState)
    (query : ((process datum oldVisit sourceIndex boundary).stateAt state).Query) :
    ((process datum oldVisit sourceIndex boundary).stateAt
      ((process datum oldVisit sourceIndex boundary).successorAt state query).val).Query := by
  cases state with
  | source =>
      have unique := germ_unique datum _ query
      cases unique
      exact branchQuery oldVisit sourceIndex boundary
        (selectedInput datum oldVisit sourceIndex boundary) 2
  | target index =>
      exact branchQuery oldVisit sourceIndex boundary
        (selectedInput datum oldVisit sourceIndex boundary) (index + 1)

theorem nextQuery_unique (state : RegistryState)
    (query : ((process datum oldVisit sourceIndex boundary).stateAt state).Query)
    (candidate : ((process datum oldVisit sourceIndex boundary).stateAt
      ((process datum oldVisit sourceIndex boundary).successorAt state query).val).Query) :
    candidate = nextQuery datum oldVisit sourceIndex boundary state query := by
  cases state with
  | source =>
      have unique := germ_unique datum _ query
      cases unique
      exact branchQuery_unique oldVisit sourceIndex boundary
        (selectedInput datum oldVisit sourceIndex boundary) 2 candidate
  | target index =>
      exact branchQuery_unique oldVisit sourceIndex boundary
        (selectedInput datum oldVisit sourceIndex boundary) (index + 1) candidate

def runtime : SourceNativeInquiryRuntime (process datum oldVisit sourceIndex boundary) where
  activationLaw :=
    { Engine.SourceNativeInquiryActivationLaw.ofUnique
        (process := process datum oldVisit sourceIndex boundary)
        (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
        (germ_unique datum _)
        (nextQuery datum oldVisit sourceIndex boundary)
        (nextQuery_unique datum oldVisit sourceIndex boundary) with
      initial := (Engine.initial (process datum oldVisit sourceIndex boundary)
        ).registeredInquiryActivation (initialInput datum oldVisit sourceIndex boundary) }

theorem initial_activation_retains_input :
    (runtime datum oldVisit sourceIndex boundary).initialState.activation.registeredInput? =
      some (initialInput datum oldVisit sourceIndex boundary) := rfl

theorem first_tick_consumes_source_core :
    ((runtime datum oldVisit sourceIndex boundary).tickAt 0).resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate RootInquiryU8CompletionRegression.failure
        (core datum oldVisit sourceIndex boundary
          (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))) := rfl

theorem runtime_consumes_core :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (core datum oldVisit sourceIndex boundary
        (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current)))
      (runtime datum oldVisit sourceIndex boundary) 0 where
  contains_core := by
    rw [first_tick_consumes_source_core]
    exact HEq.rfl

theorem runtime_core_unique {Core : Type 11} {candidate : Core}
    (resumed : SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      candidate (runtime datum oldVisit sourceIndex boundary) 0) :
    HEq candidate (core datum oldVisit sourceIndex boundary
      (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))) :=
  resumed.core_heq (runtime_consumes_core datum oldVisit sourceIndex boundary)

theorem first_macro_next_is_executed_target :
    ((runtime datum oldVisit sourceIndex boundary).stateAt 1).engine.node =
      .active (targetPresentation datum oldVisit sourceIndex boundary 2) := rfl

#print axioms runtime_consumes_core
#print axioms runtime_core_unique

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource
