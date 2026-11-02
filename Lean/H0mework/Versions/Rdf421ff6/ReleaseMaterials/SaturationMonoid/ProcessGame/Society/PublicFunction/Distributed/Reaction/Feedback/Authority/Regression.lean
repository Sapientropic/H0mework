import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Regression

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

abbrev base := Native.Regression.authorityBase
abbrev scope := Native.Regression.authorityScope
abbrev initial := Native.Regression.authorityInitial
abbrev law := Mandate.Source.law
abbrev Action := Mandate.Source.Action
def proposal := Mandate.request scope initial false (.propose true)
def offered := law.step initial proposal
def acceptance := Mandate.request scope offered true .accept
def held := law.step offered acceptance
def challenge : Action := ⟨false, [], .challenge, [.challenge], .present⟩
def prelude := [proposal, acceptance, Native.Regression.authorityIssue, challenge]
def beforeBurn := law.next initial prelude
def burn : Action := ⟨false, [], .resource, [], .use false [((), beforeBurn.stock false ())] .external⟩
def dry := law.step beforeBurn burn
def refused := Mandate.request scope dry false .revoke
def originalWord := prelude ++ [burn, refused]
def beforeExit := law.next initial originalWord
def exit := Mandate.request scope beforeExit true .exit
abbrev code := {Native.Regression.authorityCode with
  actions := [exit]
  actionLimit := 1
  bootstrap := originalWord
  historyAlphabet := []
  historyLimit := 0}
def policy : code.Policy := fun _ _ => [exit]
def rival : Opponent code := fun _ _ _ => some ⟨.activate ⟨0, by decide +kernel⟩, by decide +kernel⟩
abbrev input : Input code := ⟨rival, 2⟩
def source : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code
  reference := policy
  reference_generated := by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp [policy])
  history := [originalWord]
  original := by
    simpa only [Code.publicPrefix, if_neg (by decide +kernel : code.bootstrap ≠ [])] using
      code.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
  feedback? := some input

def bound : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) := ⟨base, scope, source, rfl, rfl⟩

def kinds (count : Nat) := (Native.Authority.challengesAt bound count).map fun record =>
  record.2.state.current.history.map LifecycleEvent.kind

theorem actual_challenge_birth_and_unfunded_withdrawal_keep_the_native_request_live :
    (source.actualExecution 0).after.technology.holder = some true ∧
      (source.actualExecution 0).after.stock false () = 0 ∧
      kinds 2 = [[.admitted, .deferred]] ∧
      (Native.Authority.fullGenerate bound 0).authority.mandates.length = 1 ∧
      Financial.outstanding source.input (Native.generate source 0).finance.current = 2 := by
  constructor <;> decide +kernel

theorem paid_actual_exit_settles_the_same_native_challenge_without_erasing_other_responsibilities :
    (source.actualExecution 2).submitted = [exit] ∧
      (source.actualExecution 2).after.technology.holder = none ∧
      (source.actualExecution 2).after.stock true () = beforeExit.stock true () - 1 ∧
      kinds 4 = [[.admitted, .deferred, .obligationTerminal]] ∧
      kinds 5 = kinds 4 ∧
      (Native.Authority.fullGenerate bound 3).authority.mandates.length = 1 ∧
      Financial.outstanding source.input (Native.generate source 3).finance.current = 2 := by
  constructor <;> decide +kernel

abbrev quiet : Cut.Term source input 0 := ⟨[none, none], (mem_sequences_iff _ _ _).mpr
  ⟨by decide +kernel, by simp [Residual.controlMenu]⟩⟩
abbrev quietBound := candidate bound input 0 rival quiet

theorem explicit_none_keeps_the_candidate_own_challenge_pending :
    (quietBound.source.actualExecution 2).submitted = [] ∧
      (quietBound.source.actualExecution 2).after.technology.holder = some true ∧
      (Native.Authority.challengesAt quietBound 5).map (fun record =>
        record.2.state.current.history.map LifecycleEvent.kind) = [[.admitted, .deferred]] := by
  constructor <;> decide +kernel

def carriedChallengeKinds (term : Cut.Term source input 0) :=
  (challengeContinuations bound input 0 rival term rfl).map fun record =>
    (record.original.val.2.state.current.history.map LifecycleEvent.kind,
      record.after.state.current.history.map LifecycleEvent.kind)

def carriedGrantKinds (term : Cut.Term source input 0) :=
  (grantContinuations bound input 0 rival term rfl).map fun record =>
    (record.original.val.2.continuation.state.history.map LifecycleEvent.kind,
      record.after.continuation.state.history.map LifecycleEvent.kind)

theorem the_original_census_precedes_the_candidate_first_word :
    carriedChallengeKinds (Cut.baseline source input 0) =
        [([.admitted, .deferred], [.admitted, .deferred, .obligationTerminal])] ∧
      carriedChallengeKinds quiet = [([.admitted, .deferred], [.admitted, .deferred])] ∧
      (grantContinuations bound input 0 rival quiet rfl).length = 1 := by
  constructor <;> decide +kernel

theorem a_paid_candidate_releases_jurisdiction_but_keeps_the_original_grant_residue :
    carriedGrantKinds (Cut.baseline source input 0) =
      [([.admitted, .deferred], [.admitted, .deferred, .bearerRelease])] ∧
      carriedGrantKinds quiet = [([.admitted, .deferred], [.admitted, .deferred])] := by
  constructor <;> decide +kernel

theorem an_already_archived_challenge_is_never_readmitted_at_a_later_cut :
    (challengeContinuations bound input 2 rival (Cut.baseline source input 2) rfl).map
      (fun record => (record.original.val.2.state.current.history.map LifecycleEvent.kind,
        record.after.state.current.history.map LifecycleEvent.kind)) =
      [([.admitted, .deferred, .obligationTerminal], [.admitted, .deferred, .obligationTerminal])] := by
  decide +kernel

def malformed : Action := {challenge with gates := []}
def malformedWord := [proposal, acceptance, Native.Regression.authorityIssue, malformed]
abbrev malformedCode := {code with bootstrap := malformedWord}
def malformedPolicy : malformedCode.Policy := fun _ _ => [exit]
def malformedSource : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := malformedCode
  reference := malformedPolicy
  reference_generated := by
    apply malformedCode.every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp [malformedPolicy])
  history := [malformedWord]
  original := by
    simpa only [Code.publicPrefix, if_neg (by decide +kernel : malformedCode.bootstrap ≠ [])] using
      malformedCode.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
def malformedBound : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) := ⟨base, scope, malformedSource, rfl, rfl⟩

theorem similar_present_without_the_signed_gate_creates_no_challenge :
    (malformedSource.actualExecution 0).after.technology.holder = some true ∧
      (Native.Authority.challengesAt malformedBound 2).isEmpty = true := by
  constructor <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Regression
