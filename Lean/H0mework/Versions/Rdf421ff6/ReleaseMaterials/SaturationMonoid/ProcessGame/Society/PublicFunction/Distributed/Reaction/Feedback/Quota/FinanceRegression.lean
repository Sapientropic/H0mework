import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Finance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Finance.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev original := Quota.Regression.original
abbrev input := Quota.Regression.input
abbrev position := Quota.Regression.position
abbrev source := Quota.Regression.source

theorem the_actual_cut_generates_complete_financial_transport :
    (generate original input 2 position 0 rfl).accepted = true :=
  every_generated_transport_is_supported original input 2 position 0 rfl

theorem certificate : Supported original input 2 position 0 rfl :=
  Outcome.certificate original input 2 position 0 rfl (generate original input 2 position 0 rfl)
    the_actual_cut_generates_complete_financial_transport

theorem generated_transport_recovers_the_actual_planned_quota :
    amount original input 2 position ≤ support source 2 position ∧
      support source 2 position = support original 2 position :=
  ⟨certificate.actual_bound, certificate.transport.same_native_quota () true false⟩

theorem the_independent_verifier_accepts_the_actual_transport :
    verify original input 2 position 0 rfl = true :=
  (independent_verifier_agrees _ _ _ _ _ _).mpr the_actual_cut_generates_complete_financial_transport

abbrev afterPaymentSource := source.atFeedbackCut 3 (fun _ _ => [])

theorem completed_payment_transports_the_original_archives :
    Native.Coupling.Match source.code source.input afterPaymentSource.input
      (Financial.accountAt source.input 6) (Financial.accountAt afterPaymentSource.input 6) :=
  Native.Coupling.State.every_prior_account_is_financially_coupled source 3 _ 6 (by decide +kernel)

theorem both_original_terminal_archives_survive_the_new_cut :
    ((Identity.financeImage source.code source.input (Financial.accountAt source.input 6)).map
        (fun debt => debt.archive.isSome)) = [true, true] ∧
      ((Identity.financeImage source.code afterPaymentSource.input (Financial.accountAt afterPaymentSource.input 6)).map
        (fun debt => debt.archive.isSome)) = [true, true] := by
  have original : ((Identity.financeImage source.code source.input (Financial.accountAt source.input 6)).map
      (fun debt => debt.archive.isSome)) = [true, true] := by decide +kernel
  exact ⟨original, (congrArg (List.map (fun debt => debt.archive.isSome))
    completed_payment_transports_the_original_archives.slots).trans original⟩

def zeroIssue : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false 0⟩
def zeroPolicy : original.code.Policy := fun _ _ => [zeroIssue]
abbrev zeroSource := original.atFeedbackCut 2 zeroPolicy

def historyDifference := Native.Coupling.generate original.code original.input zeroSource.input
  (Financial.accountAt original.input 6) (Financial.accountAt zeroSource.input 6)

def actualRecordDifferenceIndex : Option Nat :=
  match Native.Coupling.compareLists
      (Native.Coupling.eventHistory original.code original.input (Financial.accountAt original.input 6))
      (Native.Coupling.eventHistory original.code zeroSource.input (Financial.accountAt zeroSource.input 6)) with
  | .equal _ => none
  | .different index _ => some index

theorem zero_principal_does_not_hide_a_new_original_slot_or_record :
    Financial.BalanceConservation.ledgerClaims zeroSource.input
        (Financial.accountAt zeroSource.input 6).current () true false = 2 ∧
      (zeroSource.actualExecution 4).after.claims () true false = 9 ∧
      historyDifference.accepted = false ∧ historyDifference.discrepancy = some (.inl 2) ∧
      actualRecordDifferenceIndex = some 2 ∧
      Native.Coupling.verify original.code original.input zeroSource.input
        (Financial.accountAt original.input 6) (Financial.accountAt zeroSource.input 6) = false := by
  decide +kernel

def fractionalFirst : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false (1 / 2)⟩
def fractionalSecond : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false (3 / 2)⟩
abbrev splitCode : Code Bool Unit Unit Unit Unit :=
  {original.code with bootstrap := [fractionalFirst, fractionalSecond]}
def splitOpponent : Opponent splitCode := fun _ past _ => match past.length with
  | 0 => some ⟨.activate 0, by decide +kernel⟩
  | 1 => some ⟨.send 0 0, by decide +kernel⟩
  | 2 => some ⟨.deliver 0, by decide +kernel⟩
  | 3 => some ⟨.activate 0, by decide +kernel⟩
  | _ => none
abbrev splitBase : Machine Bool Unit Unit Unit Unit :=
  {Quota.Regression.base with
    code := splitCode
    opponent := splitOpponent
    feedback? := none
    feedbackOverrides := []
    history := [[fractionalFirst, fractionalSecond]]
    original := by decide +kernel}
abbrev splitSource := splitBase.withFeedback splitOpponent 3

def debtDifference := Native.Coupling.generate original.code original.input splitSource.input
  (Financial.accountAt original.input 5) (Financial.accountAt splitSource.input 5)

theorem equal_aggregate_quota_does_not_replace_the_original_debts :
    Financial.BalanceConservation.ledgerClaims splitSource.input
        (Financial.accountAt splitSource.input 5).current () true false = 2 ∧
      (splitSource.actualExecution 3).after.claims () true false = 9 ∧
      debtDifference.accepted = false ∧ debtDifference.discrepancy = some (.inl 0) := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Finance.Regression
