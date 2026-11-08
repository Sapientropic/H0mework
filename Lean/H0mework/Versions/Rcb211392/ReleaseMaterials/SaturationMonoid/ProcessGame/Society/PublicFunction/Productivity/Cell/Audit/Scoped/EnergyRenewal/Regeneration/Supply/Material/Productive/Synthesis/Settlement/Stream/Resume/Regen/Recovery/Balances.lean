import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Financial.Family.BalanceConservation Financial.Family.InstrumentProjection

private theorem action_preserves_another_key (scope : Scope) (before : Current)
    (action : JointAction) (retained : RetainsClaims action)
    (instrument : Instrument) (debtor holder : Actor)
    (other : (instrument, debtor, holder) ≠ (.delivery, supplier, receiver)) :
    ((law scope).step before action).claims instrument debtor holder = before.claims instrument debtor holder := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims before action instrument debtor holder = _
    cases operation : action.operation
    case settle code sourceDebtor targetHolder quantity =>
      have original : code = .delivery ∧ sourceDebtor = supplier ∧ targetHolder = receiver := by
        simpa only [RetainsClaims, operation] using retained
      obtain ⟨rfl, rfl, rfl⟩ := original
      simp only [RawLaw.nextClaims, operation, if_neg other, sub_zero]
    case issue => simp only [RetainsClaims, operation] at retained
    case assign => simp only [RetainsClaims, operation] at retained
    all_goals simp only [RawLaw.nextClaims, operation]
  · rfl

theorem all_other_keys_are_kept (scope : Scope) (before : Current) (actions : List JointAction)
    (retained : ∀ action ∈ actions, RetainsClaims action)
    (instrument : Instrument) (debtor holder : Actor)
    (other : (instrument, debtor, holder) ≠ (.delivery, supplier, receiver)) :
    ((law scope).next before actions).claims instrument debtor holder = before.claims instrument debtor holder := by
  change ((law scope).execute before 0 actions).final.claims instrument debtor holder = _
  generalize 0 = index
  induction actions generalizing before index with
  | nil => rfl
  | cons action rest later =>
    exact (later ((law scope).step before action)
      (fun a h => retained a (List.mem_cons_of_mem _ h)) (index + 1)).trans
        (action_preserves_another_key scope before action (retained action List.mem_cons_self) _ _ _ other)

namespace Runtime

variable {seed : Seed} {oldRequests : Requests.Source} {permission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests permission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  (cut : Cut source requests authority index) (offset : Nat)

local notation "permit" => permissionAt seed requests permission (index + 1 + (offset + 1)) (run cut offset)

theorem actual_repayment_preserves_every_other_claim_address
    (ready : OpeningAt cut)
    (choice : OptionAt seed.basis.origin.scope permit (run cut offset).raw)
    (selected : selection seed permit (run cut offset) = .repay choice)
    (instrument : Instrument) (debtor holder : Actor)
    (other : (instrument, debtor, holder) ≠ (.delivery, supplier, receiver)) :
    (execution cut offset).after.claims instrument debtor holder =
      (execution cut offset).before.claims instrument debtor holder := by
  rw [actual_after, original_actual_before, after]
  change (admittedStep cut offset (run cut offset)).raw.claims _ _ _ = _
  rw [admitted_step_when_ready cut ready, step_uses_the_selected_word, word, selected]
  exact all_other_keys_are_kept _ _ _ choice.property.2.2.2.1 _ _ _ other

theorem the_native_delivery_slice_is_the_actual_paid_slice
    (compatible : Compatible Finance.sources (input cut) (priorAccount cut offset).current)
    (originalOpening : Financial.Family.ledgerClaims Finance.sources (priorAccount cut offset).current .delivery =
      (execution cut offset).before.claims .delivery) :
    Financial.Family.ledgerClaims Finance.sources (account cut offset).current .delivery =
      (execution cut offset).after.claims .delivery := by
  rw [original_actual_before] at originalOpening
  rw [actual_after, after]
  have sourceOpening := originalOpening.trans
    (congrArg (fun raw : Current => raw.claims .delivery) (own_current cut offset)).symm
  have sourceAfter := consume_visit_source_slice Finance.sources (input cut)
    (handoff (baseCut := baseCut) index + offset) (priorAccount cut offset) .delivery compatible sourceOpening
  exact sourceAfter.trans (congrArg (fun raw : Current => raw.claims .delivery) (own_current cut (offset + 1)))

theorem the_original_native_delivery_balance_is_cleared
    (ready : OpeningAt cut)
    (choice : OptionAt seed.basis.origin.scope permit (run cut offset).raw)
    (selected : selection seed permit (run cut offset) = .repay choice)
    (compatible : Compatible Finance.sources (input cut) (priorAccount cut offset).current)
    (originalOpening : Financial.Family.ledgerClaims Finance.sources (priorAccount cut offset).current .delivery =
      (execution cut offset).before.claims .delivery) :
    Financial.Family.ledgerClaims Finance.sources (account cut offset).current .delivery supplier receiver = 0 := by
  have paid := (actual_repayment_preserves_the_request cut offset ready choice selected).1
  exact (congrFun (congrFun (the_native_delivery_slice_is_the_actual_paid_slice cut offset compatible originalOpening)
    supplier) receiver).trans paid

end Runtime
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery
