import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.OrderRegression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

abbrev initial : Mandate.Source.Current := {Native.Regression.authorityInitial with clock := 1}
def proposal := Mandate.request Native.Regression.authorityScope initial false (.propose true)
def acceptance := Mandate.request Native.Regression.authorityScope (Mandate.Source.law.step initial proposal) true .accept
def challenge : Mandate.Source.Action := ⟨false, [], .challenge, [.challenge], .present⟩

def servedPrelude := [proposal, acceptance, Native.Regression.authorityIssue,
  Mandate.Source.necessity, Mandate.Source.maintenance, challenge]
def beforeBurn := Mandate.Source.law.next initial servedPrelude
def burn : Mandate.Source.Action := ⟨false, [], .resource, [], .use false [((), beforeBurn.stock false ())] .external⟩
def dry := Mandate.Source.law.step beforeBurn burn
def refused := Mandate.request Native.Regression.authorityScope dry false .revoke
def originalWord := servedPrelude ++ [burn, refused]
def current := Mandate.Source.law.next initial originalWord
def exit := Mandate.request Native.Regression.authorityScope current true .exit
def waste : Mandate.Source.Action := ⟨true, [], .resource, [], .use true [((), 1)] .external⟩
abbrev code := {Native.Regression.authorityCode with
  initial := initial
  actions := [exit, waste]
  actionLimit := 2
  bootstrap := originalWord
  historyAlphabet := []
  historyLimit := 0}
def policy : code.Policy := fun _ _ => [exit, waste]
def efficient : code.Policy := fun _ _ => [exit]
theorem efficient_generated : efficient ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [efficient])
def rival : Opponent code := fun _ _ _ => some ⟨.activate ⟨0, by decide +kernel⟩, by decide +kernel⟩
abbrev input : Input code := ⟨rival, 1⟩
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
    (Technology := Unit) (Instrument := Unit) := ⟨Native.Regression.authorityBase, Native.Regression.authorityScope, source, rfl, rfl⟩
abbrev reference := Cut.baseline source input 0

def efficientTerm : Cut.Term source input 0 := ⟨[some efficient], (mem_sequences_iff _ _ _).mpr
  ⟨by decide +kernel, by
    change ∀ control ∈ [some efficient], control ∈ Residual.controlMenu source
    intro control member
    have same := List.mem_singleton.mp member
    subst control
    change some efficient ∈ Residual.controlMenu source
    exact List.mem_cons_of_mem none (List.mem_cons_of_mem source.policy?
      (List.mem_append_right _ (List.mem_map.mpr ⟨efficient, efficient_generated, rfl⟩)))⟩⟩

def quietTerm : Cut.Term source input 0 := ⟨[none], (mem_sequences_iff _ _ _).mpr
  ⟨by decide +kernel, by simp [Residual.controlMenu]⟩⟩
abbrev paid := generate bound input 0 rival efficientTerm rfl
abbrev pending := generate bound input 0 rival quietTerm rfl

def removed : Manifest Bool Unit Mandate.Source.Port Unit Unit := {paid with candidateChallenges := []}
def duplicated : Manifest Bool Unit Mandate.Source.Port Unit Unit :=
  {pending with candidateChallenges := pending.candidateChallenges ++ pending.candidateChallenges}

theorem reference_is_feasible : Cut.Feasible source input 0 reference := by
  unfold Cut.Feasible Cut.LocalValidity Cut.Service
  decide +kernel

abbrev disposition := Selection.generateSelection bound input 0 rfl rfl reference
abbrev chosen := Selection.choiceFrom bound input 0 rfl reference disposition.outcome
  reference_is_feasible
abbrev chosenBound := candidate bound input 0 rival chosen.policy.term

def checks : List (String × Bool) :=
  [ ("actual_paid_withdrawal_strictly_reduces_native_liability", decide (Lawful.NoWorse paid pending ∧ ¬ Lawful.NoWorse pending paid)),
    ("paid_archive_retains_all_original_admissions", decide ((Lawful.inventory paid).admitted.Perm (Lawful.inventory pending).admitted)),
    ("grant_bearer_release_keeps_both_grant_residues", decide ((Lawful.inventory paid).due.length = 2)),
    ("deleting_a_real_terminal_archive_is_rejected", !decide (Lawful.NoWorse removed paid)),
    ("duplicating_a_real_unpaid_birth_is_rejected", !decide (Lawful.NoWorse duplicated pending)),
    ("full_manifest_verifier_rejects_omitted_archive", !(verify bound input 0 rival efficientTerm rfl removed)),
    ("nonempty_original_grant_and_challenge", decide ((generate bound input 0 rival reference rfl).originalGrants.length = 1 ∧
      (generate bound input 0 rival reference rfl).originalChallenges.length = 1)),
    ("reference_feasible", @decide (Cut.Feasible source input 0 reference) (by unfold Cut.Feasible Cut.LocalValidity Cut.Service; infer_instance)),
    ("efficient_feasible", @decide (Cut.Feasible source input 0 efficientTerm) (by unfold Cut.Feasible Cut.LocalValidity Cut.Service; infer_instance)),
    ("efficient_economic_strict", decide (Cut.Better source input 0 reference efficientTerm)),
    ("efficient_full_native_no_worse", @decide (∀ table ∈ Cut.tables source input 0,
      Selection.native bound input 0 rfl table efficientTerm reference) (by unfold Selection.native; infer_instance)),
    ("new_unpaid_admission_needs_its_own_burden_capacity", !decide (({admitted := [true], due := [true]} : Lawful.Inventory Bool).NoWorse ⟨[], []⟩)),
    ("chosen_satisfies_actual_strict_full_contract", @decide (Selection.Better bound input 0 rfl reference chosen.policy.term) (Selection.decidableBetter bound input 0 rfl reference chosen.policy.term)),
    ("chosen_source_actually_submits_efficient_exit", decide ((chosenBound.source.actualExecution 2).submitted = [exit])),
    ("chosen_source_strict_material_dividend", decide ((chosenBound.source.actualExecution 2).after.stock true () = 8 ∧
      ((candidate bound input 0 rival reference).source.actualExecution 2).after.stock true () = 7)),
    ("chosen_source_keeps_original_principal", decide (Financial.outstanding chosenBound.source.input
      (Native.generate chosenBound.source 2).finance.current = 2)),
    ("independent_verifier_accepts_the_raw_external_proposal", Selection.verify bound input 0 rfl reference efficientTerm),
    ("independent_global_verifier_accepts_actual_choice", Selection.verify bound input 0 rfl reference chosen.policy.term),
    ("independent_global_verifier_rejects_dominated_original", !(Selection.verify bound input 0 rfl reference reference)) ]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.OrderRegression
