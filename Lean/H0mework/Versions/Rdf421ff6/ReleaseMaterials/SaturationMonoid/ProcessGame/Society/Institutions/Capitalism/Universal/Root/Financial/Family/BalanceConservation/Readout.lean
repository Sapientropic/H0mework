import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

theorem admit_ledgerClaims (state : (process sources).GeneratedState) (claim : Claim sources)
    (instrument : Instrument) (debtor holder : Party) :
    ledgerClaims sources (admit sources state claim).current instrument debtor holder =
      ledgerClaims sources state.current instrument debtor holder +
        if (instrument, debtor, holder) = (claim.2.instrument, claim.2.debtor, claim.2.holder)
          then claim.2.quantity else 0 := by
  change ((state.current.slots ++ [ObligationSlot.live (admission sources claim).toObligation]).map _).sum = _
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  change (if claim.2.instrument = instrument ∧ claim.2.debtor = debtor then
    Financial.BalanceConservation.shareAt (sources claim.1) (initialBalance (sources claim.1) claim.2) holder else 0) = _
  rw [Financial.BalanceConservation.shareAt_initial]
  by_cases first : claim.2.instrument = instrument <;>
    by_cases second : claim.2.debtor = debtor <;>
      by_cases third : claim.2.holder = holder <;> simp_all [Prod.mk.injEq, eq_comm]

theorem cross_ledgerClaims (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation) (boundary : Boundary sources obligation)
    (instrument : Instrument) (debtor holder : Party) :
    ledgerClaims sources (cross sources state index obligation present boundary).current instrument debtor holder =
      ledgerClaims sources state.current instrument debtor holder -
        slotClaims sources (.live obligation) instrument debtor holder +
        if obligation.content.2.instrument = instrument ∧ obligation.content.2.debtor = debtor then
          (boundary.event sources).after sources holder else 0 := by
  unfold ledgerClaims
  change ((state.current.slots.set index (Boundary.disposition sources boundary).targetSlot).map _).sum = _
  rw [List.map_set, List.sum_set']
  simp only [List.length_map, index.isLt, ↓reduceDIte, List.getElem_map]
  have row : state.current.slots[index.val] = .live obligation := present
  rw [row]
  have changed : slotClaims sources (Boundary.disposition sources boundary).targetSlot instrument debtor holder =
      if obligation.content.2.instrument = instrument ∧ obligation.content.2.debtor = debtor then
        (boundary.event sources).after sources holder else 0 := by
    unfold slotClaims
    rw [boundary_claim, boundary_balance]
  rw [changed]
  ring

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation
