import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consume
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Word
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open Source.Program
open private consumeItems consumeItems_run from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

def PaymentWord (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ request ∈ word, ∃ instrument debtor holder quantity,
    request.operation = .settle instrument debtor holder quantity ∧ 0 ≤ quantity

omit [DecidableEq Good] [DecidableEq Port] in
theorem payment_word_value_nonnegative (word : RawEvent Party Good Port Technology Instrument)
    (payments : PaymentWord word) (instrument : Instrument) (debtor holder : Party) :
    0 ≤ wordValue word instrument debtor holder := by
  apply List.sum_nonneg
  intro amount member
  obtain ⟨request,listed,rfl⟩ := List.mem_map.mp member
  obtain ⟨source,borrower,creditor,quantity,operation,positive⟩ := payments request listed
  simp only [requestValue,operation]
  split_ifs <;> first | exact positive | exact le_refl 0

theorem the_original_item_fold_exhausts_the_entire_source_settlement_inventory
    (items : List (ActualItem input depth count))
    (payments : PaymentWord (items.map (fun item => (item.instruction input depth count).request)))
    (accepted : ∀ item ∈ items, (item.interpreter input depth count).Valid
      (item.instruction input depth count).before (item.instruction input depth count).request)
    (state : (process input depth count).GeneratedState)
    (matched : ∀ instrument debtor holder, ledgerClaims input depth count state.current instrument debtor holder =
      wordValue (items.map (fun item => (item.instruction input depth count).request)) instrument debtor holder) :
    (∀ instrument debtor holder,
      ledgerClaims input depth count (consumeItems input depth count items state).current instrument debtor holder = 0) ∧
    (consumeItems input depth count items state).current.slots.map (slotClaim input depth count) =
      state.current.slots.map (slotClaim input depth count) := by
  induction items generalizing state with
  | nil =>
      exact ⟨fun instrument debtor holder => matched instrument debtor holder,rfl⟩
  | cons item tail ih =>
      obtain ⟨instrument,debtor,holder,quantity,operation,positive⟩ := payments (item.instruction input depth count).request (by simp only [List.map_cons]; exact List.mem_cons_self)
      have tailPayments : PaymentWord (tail.map (fun next => (next.instruction input depth count).request)) := by
        intro request listed
        exact payments request (List.mem_cons_of_mem _ listed)
      have funded : quantity ≤ ledgerClaims input depth count state.current instrument debtor holder := by
        rw [matched]
        change quantity ≤ requestValue (item.instruction input depth count).request instrument debtor holder +
          wordValue (tail.map (fun next => (next.instruction input depth count).request)) instrument debtor holder
        simp only [requestValue,operation,and_self,↓reduceIte]
        exact le_add_of_nonneg_right (payment_word_value_nonnegative _ tailPayments instrument debtor holder)
      let after := (consume input depth count item state).next input depth count
      have tailMatched : ∀ observed bearer creditor,
          ledgerClaims input depth count after.current observed bearer creditor =
            wordValue (tail.map (fun next => (next.instruction input depth count).request)) observed bearer creditor := by
        intro observed bearer creditor
        rw [(the_original_consumer_pays_the_whole_funded_share input depth count item instrument observed debtor holder bearer creditor
          quantity operation (accepted item (List.mem_cons_self)) state funded).1,matched]
        change requestValue (item.instruction input depth count).request observed bearer creditor +
          wordValue (tail.map (fun next => (next.instruction input depth count).request)) observed bearer creditor +
          paymentDelta instrument debtor holder quantity observed bearer creditor = _
        simp only [requestValue,operation,paymentDelta]
        split_ifs <;> ring
      have rest := ih tailPayments (fun next listed => accepted next (List.mem_cons_of_mem _ listed)) after tailMatched
      refine ⟨rest.1,rest.2.trans ?_⟩
      exact (the_original_consumer_pays_the_whole_funded_share input depth count item instrument instrument debtor holder debtor holder
        quantity operation (accepted item (List.mem_cons_self)) state funded).2

theorem the_original_finite_settlement_history_is_preserved
    (items : List (ActualItem input depth count)) (state : (process input depth count).GeneratedState) :
    state.current.history <+: (consumeItems input depth count items state).current.history := by
  rw [(consumeItems_run input depth count items state).history_eq]
  exact List.prefix_append _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
