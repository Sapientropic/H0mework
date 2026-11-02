import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.InputOrigin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Rank

/-! One registry owns the registered input, its no-fresh accounting ingress,
and all subsequent native debt roots.  An index is only a finite observation
of this source recursion, never an authority supplied to Engine.ask. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (positive : 0 < ProgrammeSource.registrationSize input)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

inductive Stage
  | input | ingress | account (count : Nat)

def registryPresentation : Stage → RootInquiryStatePresentation
  | .input => inputPresentation input oldVisit sourceIndex boundary
  | .ingress => ingressPresentation input 1
  | .account count => (frames input 1 count).presentation input

theorem input_ne_account (count : Nat) :
    (inputPresentation input oldVisit sourceIndex boundary).erase ≠
      ((frames input 1 count).presentation input).erase := by
  intro same
  have cards := congrArg erasedEntryCard same
  rw [input_entry_card] at cards
  have lower := frames_entry_lower input 1 count
  change 2 ≤ erasedEntryCard ((frames input 1 count).presentation input).erase at lower
  omega

def process : SourceNativeInquiryEngineProcess where
  State := Stage
  stateAt := fun stage => .active (registryPresentation input oldVisit sourceIndex boundary stage)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive same
    cases leftActive
    cases rightActive
    cases left with
    | input =>
        cases right with
        | input => rfl
        | ingress => exact (input_ne_ingress input oldVisit sourceIndex boundary same).elim
        | account count => exact (input_ne_account input oldVisit sourceIndex boundary count same).elim
    | ingress =>
        cases right with
        | input => exact (input_ne_ingress input oldVisit sourceIndex boundary same.symm).elim
        | ingress => rfl
        | account count => exact (ingress_ne_frame input 1 (frames input 1 count) same).elim
    | account first =>
        cases right with
        | input => exact (input_ne_account input oldVisit sourceIndex boundary first same.symm).elim
        | ingress => exact (ingress_ne_frame input 1 (frames input 1 first) same.symm).elim
        | account second => exact congrArg Stage.account (frames_erase_injective input 1 same)
  initial := .input
  successorAt := by
    intro stage query
    cases stage with
    | input => exact ⟨.ingress, input_successor_valid input oldVisit sourceIndex boundary positive query⟩
    | ingress => exact ⟨.account 0, ingress_successor_valid input 1 query⟩
    | account count => exact ⟨.account (count + 1), (frames input 1 count).successor_valid input query⟩

def initialInput : Engine.SourceNativeInquiryRegisteredInputAt
    (Engine.initial (process input positive oldVisit sourceIndex boundary)) :=
  InputSource.registeredInput (datum input) (InputSource.visit (datum input) oldVisit sourceIndex boundary)

def nextQuery (stage : Stage)
    (_query : ((process input positive oldVisit sourceIndex boundary).stateAt stage).Query) :
    ((process input positive oldVisit sourceIndex boundary).stateAt
      ((process input positive oldVisit sourceIndex boundary).successorAt stage _query).val).Query := by
  cases stage with
  | input => exact PUnit.unit
  | ingress => exact (initialFrame input 1).query input
  | account count => exact (frames input 1 (count + 1)).query input

theorem nextQuery_unique (stage : Stage)
    (query : ((process input positive oldVisit sourceIndex boundary).stateAt stage).Query)
    (candidate : ((process input positive oldVisit sourceIndex boundary).stateAt
      ((process input positive oldVisit sourceIndex boundary).successorAt stage query).val).Query) :
    candidate = nextQuery input positive oldVisit sourceIndex boundary stage query := by
  cases stage <;> cases candidate <;> rfl

/-- The registered source fixes this process and activation. The real
accounting-ingress receipt carries its initial balance disposition. -/
def sourceRuntime :
    SourceNativeInquiryRuntime (process input positive oldVisit sourceIndex boundary) where
  activationLaw :=
    { Engine.SourceNativeInquiryActivationLaw.ofUnique
        (process := process input positive oldVisit sourceIndex boundary)
        (inputQuery input oldVisit sourceIndex boundary)
        (input_query_unique input oldVisit sourceIndex boundary)
        (nextQuery input positive oldVisit sourceIndex boundary)
        (nextQuery_unique input positive oldVisit sourceIndex boundary) with
      initial := (Engine.initial (process input positive oldVisit sourceIndex boundary)).registeredInquiryActivation
        (initialInput input positive oldVisit sourceIndex boundary) }

/-- The established zero-genesis entry is exactly the same original runtime. -/
def runtime (_initialZero : input.initial.claims = fun _ _ _ => 0) :
    SourceNativeInquiryRuntime (process input positive oldVisit sourceIndex boundary) :=
  sourceRuntime input positive oldVisit sourceIndex boundary

theorem the_zero_genesis_entry_is_the_literal_source_runtime
    (initialZero : input.initial.claims = fun _ _ _ => 0) :
    runtime input positive oldVisit sourceIndex boundary initialZero =
      sourceRuntime input positive oldVisit sourceIndex boundary := rfl

theorem activation_retains_full_input (initialZero : input.initial.claims = fun _ _ _ => 0) :
    (runtime input positive oldVisit sourceIndex boundary initialZero).initialState.activation.registeredInput? =
      some (initialInput input positive oldVisit sourceIndex boundary) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
