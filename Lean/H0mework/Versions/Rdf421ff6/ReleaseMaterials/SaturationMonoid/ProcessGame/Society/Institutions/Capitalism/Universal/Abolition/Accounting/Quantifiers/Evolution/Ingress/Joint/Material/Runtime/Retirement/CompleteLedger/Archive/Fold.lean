import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Scan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Fold
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

open private consumeItems from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

theorem a_zero_survives_the_complete_actual_payment_inventory_only_if_untouched
    (items : List (ActualItem input depth count))
    (payments : PaymentWord (items.map (fun item => (item.instruction input depth count).request)))
    (accepted : ∀ item ∈ items, (item.interpreter input depth count).Valid
      (item.instruction input depth count).before (item.instruction input depth count).request)
    (state : (process input depth count).GeneratedState)
    (index : Nat) (survivor : AdmittedObligation (vocabulary input depth count))
    (zero : survivor.residual = 0)
    (present : (consumeItems input depth count items state).current.slots[index]? = some (.live survivor)) :
    state.current.slots[index]? = some (.live survivor) ∧
      ∀ item ∈ items, readReview input depth count survivor.content item = none := by
  induction items generalizing state with
  | nil => exact ⟨present,fun _ listed => (List.not_mem_nil listed).elim⟩
  | cons item tail ih =>
      have tailPayments : PaymentWord (tail.map (fun next => (next.instruction input depth count).request)) := by
        intro request listed
        exact payments request (List.mem_cons_of_mem _ listed)
      have rest := ih tailPayments (fun next listed => accepted next (List.mem_cons_of_mem _ listed))
        ((consume input depth count item state).next input depth count) present
      obtain ⟨instrument,debtor,holder,quantity,operation,_⟩ :=
        payments (item.instruction input depth count).request (by simp only [List.map_cons]; exact List.mem_cons_self)
      have first := a_zero_survives_one_actual_payment_only_without_a_matching_review input depth count item state
        instrument debtor holder quantity operation (accepted item List.mem_cons_self) index survivor zero rest.1
      refine ⟨first.1,?_⟩
      intro original listed
      rcases List.mem_cons.mp listed with same | later
      · subst original
        exact first.2
      · exact rest.2 original later

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
