import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Instruction
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

def slotClaims (slot : ObligationSlot (vocabulary input depth count))
    (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  if (slotClaim input depth count slot).instrument input depth count = instrument ∧
      (slotClaim input depth count slot).debtor input depth count = debtor then
    slotBalance input depth count slot creditor else 0

def ledgerClaims (state : ResponsibilityState (vocabulary input depth count))
    (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  (state.slots.map (fun slot => slotClaims input depth count slot instrument debtor creditor)).sum

theorem slotClaims_nonnegative (state : (process input depth count).GeneratedState)
    (slot : ObligationSlot (vocabulary input depth count)) (member : slot ∈ state.current.slots)
    (instrument : Instrument) (debtor creditor : Party) :
    0 ≤ slotClaims input depth count slot instrument debtor creditor := by
  unfold slotClaims
  split_ifs
  · exact (generated_sound input depth count state slot member).2 creditor
  · exact le_refl 0

@[simp] theorem slotClaims_terminal (archive : TerminalArchive (vocabulary input depth count))
    (instrument : Instrument) (debtor creditor : Party) :
    slotClaims input depth count (.terminal archive) instrument debtor creditor = 0 := by
  simp [slotClaims, slotBalance]

theorem cross_ledgerClaims (state : (process input depth count).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input depth count))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary input depth count obligation)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims input depth count
        (state.step (process input depth count) (.cross index obligation present boundary)).current
        instrument debtor creditor =
      ledgerClaims input depth count state.current instrument debtor creditor -
        slotClaims input depth count (.live obligation) instrument debtor creditor +
        if obligation.content.instrument input depth count = instrument ∧
            obligation.content.debtor input depth count = debtor then
          boundary.event.after input depth count creditor else 0 := by
  unfold ledgerClaims
  change ((state.current.slots.set index (boundaryDisposition input depth count boundary).targetSlot).map _).sum = _
  rw [List.map_set, List.sum_set']
  simp only [List.length_map, index.isLt, ↓reduceDIte, List.getElem_map]
  have row : state.current.slots[index.val] = .live obligation := present
  rw [row]
  have changed : slotClaims input depth count (boundaryDisposition input depth count boundary).targetSlot
      instrument debtor creditor =
      if obligation.content.instrument input depth count = instrument ∧
          obligation.content.debtor input depth count = debtor then
        boundary.event.after input depth count creditor else 0 := by
    unfold slotClaims
    rw [boundary_claim, boundary_balance]
  rw [changed]
  ring

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
