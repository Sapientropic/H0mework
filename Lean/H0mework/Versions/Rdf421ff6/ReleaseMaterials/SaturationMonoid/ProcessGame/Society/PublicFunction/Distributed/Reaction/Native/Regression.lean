import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Principal

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

abbrev source := Reaction.Regression.source

def serviceKinds {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (source : Machine Party Good Port Technology Instrument) (depth : Nat) (index : Slot source) : List Bool :=
  ((generate source depth).services index).state.slots.map fun slot => match slot with
    | .live _ => false | .terminal _ => true

theorem actual_selected_service_has_a_native_archive :
    serviceKinds source 0 ⟨0, by decide⟩ = [true] ∧
      serviceKinds (source.withSide .original) 0 ⟨0, by decide⟩ = [true] := by decide +kernel

abbrev poorCode := {Reaction.Regression.code with initial := PublicFunction.Regression.initial 0}
def poorPolicy : poorCode.Policy := fun _ _ => [Reaction.Regression.need]
def poor : Machine Bool Unit Unit Unit Unit where
  code := poorCode
  reference := poorPolicy
  reference_generated := by
    apply poorCode.every_local_policy_is_enumerated
    intro key _
    apply (mem_words_iff _ _ _).mpr
    simp [poorPolicy]
  history := []
  original := by simp [Code.histories, poorCode, Reaction.Regression.code, sequences, Code.historyLegal]
  opponent := fun _ _ _ => some ⟨.activate 0, by simp [poorCode, Reaction.Regression.code, Distributed.Regression.code]⟩
  side := .original

abbrev shortTask := {Reaction.Regression.code.task with deadline := 1}
abbrev shortCode := {Reaction.Regression.code with task := shortTask}
def shortSource : Machine Bool Unit Unit Unit Unit where
  code := shortCode
  reference := Reaction.Regression.reference
  reference_generated := Reaction.Regression.reference_is_generated
  history := []
  original := by simp [Code.histories, shortCode, Reaction.Regression.code, sequences, Code.historyLegal]
  opponent := fun _ _ _ => some ⟨.activate 0, by simp [shortCode, Reaction.Regression.code, Distributed.Regression.code]⟩
  side := .original

theorem refused_or_late_payment_cannot_close_native_service :
    serviceKinds poor 0 ⟨0, by decide⟩ = [false] ∧
      serviceKinds shortSource 0 ⟨0, by decide⟩ = [false] := by decide +kernel

def issue : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false 2⟩
abbrev financeCode := {Reaction.Regression.code with
  initial := {PublicFunction.Regression.initial 4 with claims := fun _ _ _ => 0}
  actions := [issue, Reaction.Regression.need]}
def financedPolicy : financeCode.Policy := fun _ _ => [issue, Reaction.Regression.need]
def financed : Machine Bool Unit Unit Unit Unit where
  code := financeCode
  reference := financedPolicy
  reference_generated := by
    apply financeCode.every_local_policy_is_enumerated
    intro key _
    apply (mem_words_iff _ _ _).mpr
    simp [financedPolicy]
  history := []
  original := by simp [Code.histories, financeCode, Reaction.Regression.code, sequences, Code.historyLegal]
  opponent := fun _ _ _ => some ⟨.activate 0, by simp [financeCode, Reaction.Regression.code, Distributed.Regression.code]⟩
  side := .original

theorem actual_new_issue_is_native_while_service_is_settled :
    serviceKinds financed 0 ⟨0, by decide⟩ = [true] ∧
      (generate financed 0).finance.current.slots.length = 1 ∧
      Financial.outstanding financed.input (generate financed 0).finance.current = 2 ∧
      (generate financed 1).finance.current.slots.length = 2 ∧
      Financial.outstanding financed.input (generate financed 1).finance.current = 4 ∧
      ((generate financed 1).services ⟨0, by decide⟩).state = ((generate financed 0).services ⟨0, by decide⟩).state := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact every_settled_service_keeps_its_first_archive financed 0 1 _
    ((native_terminal_iff_actual_payment financed _ 1).mpr ⟨0, by omega, by decide +kernel⟩)

abbrev authorityBase := Mandate.Source.base
abbrev authorityScope := Mandate.Source.scope
abbrev authorityInitial : Mandate.Source.Current := {Mandate.Source.initial with stock := fun _ _ => 10, claims := fun _ _ _ => 0}
def authorityIssue : Mandate.Source.Action := ⟨false, [], .resource, [], .issue () false true 2⟩
abbrev originalWord := Mandate.Regression.lifecycleWord ++ [authorityIssue]

def authorityCode : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  law := Mandate.Source.law
  initial := authorityInitial
  task := Mandate.Source.task
  actions := []
  actionLimit := 0
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => false
  readLocal := fun _ _ => 0
  historyAlphabet := [originalWord]
  historyLimit := 1
  eventAlphabet := [.activate 0]
  eventLimit := 1
  eligible := fun _ => true
  parties := [false, true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro party; cases party <;> simp
  goods_cover := by intro good; cases good; simp
  instruments_cover := by intro instrument; cases instrument; simp

def authorityPolicy : authorityCode.Policy := fun _ _ => []
def authoritySource : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := authorityCode
  reference := authorityPolicy
  reference_generated := by
    apply authorityCode.every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp [authorityPolicy])
  history := [originalWord]
  original := by decide +kernel
  opponent := fun _ _ _ => none
  side := .original

def bound : Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) :=
  ⟨authorityBase, authorityScope, authoritySource, rfl, rfl⟩

theorem actual_exit_keeps_all_original_services_grants_and_new_principal :
    (authoritySource.actualExecution 0).after.technology.holder = none ∧
      serviceKinds authoritySource 0 ⟨0, by decide⟩ = [false] ∧
      serviceKinds authoritySource 0 ⟨1, by decide⟩ = [false] ∧
      (Authority.generate bound 0).mandates.length = 1 ∧
      (Authority.generate bound 1).mandates.length = 1 ∧
      (generate authoritySource 0).finance.current.slots.length = 1 ∧
      Financial.outstanding authoritySource.input (generate authoritySource 1).finance.current = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

abbrev publicNativeReactionFacade := Native.Runtime.facade source
abbrev publicNativeAuthorityFacade := Native.AuthorityRuntime.facade bound

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Regression
