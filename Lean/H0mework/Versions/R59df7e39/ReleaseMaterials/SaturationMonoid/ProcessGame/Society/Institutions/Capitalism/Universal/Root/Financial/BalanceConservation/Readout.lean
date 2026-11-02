import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Principal
import Mathlib.Data.List.Nodup

/-! Linear matrix reads of the shares already held in each native slot. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle Source.Program
open scoped BigOperators

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def shareAt (balance : Balance input) (creditor : Party) : ℚ :=
  balance creditor

def slotClaims (slot : ObligationSlot (vocabulary input))
    (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  if (slotClaim input slot).instrument = instrument ∧
      (slotClaim input slot).debtor = debtor then
    shareAt input (slotBalance input slot) creditor else 0

def ledgerClaims (state : ResponsibilityState (vocabulary input))
    (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  (state.slots.map (fun slot => slotClaims input slot instrument debtor creditor)).sum

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem holderParty_injective : Function.Injective (holderParty input) := fun _ _ same => same

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem shareAt_key (balance : Balance input) (holder : Holder input) :
    shareAt input balance (holderParty input holder) = balance holder := rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
@[simp] theorem shareAt_zero (creditor : Party) : shareAt input 0 creditor = 0 := rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem shareAt_add (left right : Balance input) (creditor : Party) :
    shareAt input (left + right) creditor = shareAt input left creditor + shareAt input right creditor := rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem shareAt_sub (left right : Balance input) (creditor : Party) :
    shareAt input (left - right) creditor = shareAt input left creditor - shareAt input right creditor := rfl

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem shareAt_single (holder : Holder input) (quantity : ℚ) (creditor : Party) :
    shareAt input (Finsupp.single holder quantity) creditor =
      if holderParty input holder = creditor then quantity else 0 := Finsupp.single_apply

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem shareAt_pay (balance : Balance input) (holder : Holder input)
    (quantity : ℚ) (creditor : Party) :
    shareAt input (pay input balance holder quantity) creditor =
      shareAt input balance creditor - if holderParty input holder = creditor then quantity else 0 := by
  change pay input balance holder quantity creditor = balance creditor - if holder = creditor then quantity else 0
  rw [pay_apply]
  by_cases same : creditor = holder
  · subst creditor; rfl
  · rw [if_neg same, if_neg (Ne.symm same)]

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem shareAt_assign (balance : Balance input) (sender recipient : Holder input)
    (quantity : ℚ) (creditor : Party) :
    shareAt input (assign input balance sender recipient quantity) creditor =
      shareAt input balance creditor - (if holderParty input sender = creditor then quantity else 0) +
        if holderParty input recipient = creditor then quantity else 0 := by
  change assign input balance sender recipient quantity creditor =
    balance creditor - (if sender = creditor then quantity else 0) + if recipient = creditor then quantity else 0
  rw [assign_apply]
  by_cases first : creditor = sender <;> by_cases second : creditor = recipient <;>
    simp_all [eq_comm]

omit [DecidableEq Port] in
theorem shareAt_initial (claim : IssuedClaim input) (creditor : Party) :
    shareAt input (initialBalance input claim) creditor =
      if claim.holder = creditor then claim.quantity else 0 := by
  change 0 + (if creditor = claim.holder then claim.quantity else 0) = _
  simp only [zero_add, eq_comm]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem shareAt_nonnegative (balance : Balance input) (nonnegative : Nonnegative input balance)
    (creditor : Party) : 0 ≤ shareAt input balance creditor := nonnegative creditor

theorem slotClaims_nonnegative (state : (process input).GeneratedState)
    (slot : ObligationSlot (vocabulary input)) (member : slot ∈ state.current.slots)
    (instrument : Instrument) (debtor creditor : Party) :
    0 ≤ slotClaims input slot instrument debtor creditor := by
  unfold slotClaims
  split_ifs
  · exact shareAt_nonnegative input _ (generated_sound input state slot member).2 creditor
  · exact le_refl 0

@[simp] theorem slotClaims_terminal (archive : TerminalArchive (vocabulary input))
    (instrument : Instrument) (debtor creditor : Party) :
    slotClaims input (.terminal archive) instrument debtor creditor = 0 := by
  simp [slotClaims, slotBalance]

theorem admit_ledgerClaims (state : (process input).GeneratedState) (claim : IssuedClaim input)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims input (admit input state claim).current instrument debtor creditor =
      ledgerClaims input state.current instrument debtor creditor +
        if (instrument, debtor, creditor) = (claim.instrument, claim.debtor, claim.holder)
          then claim.quantity else 0 := by
  change ((state.current.slots ++ [ObligationSlot.live (admission input claim).toObligation]).map _).sum = _
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  congr 1
  change (if claim.instrument = instrument ∧ claim.debtor = debtor then
    shareAt input (initialBalance input claim) creditor else 0) = _
  rw [shareAt_initial]
  by_cases first : claim.instrument = instrument <;>
    by_cases second : claim.debtor = debtor <;>
      by_cases third : claim.holder = creditor <;> simp_all [Prod.mk.injEq, eq_comm]

theorem cross_ledgerClaims (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary input obligation)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims input (cross input state index obligation present boundary).current instrument debtor creditor =
      ledgerClaims input state.current instrument debtor creditor -
        slotClaims input (.live obligation) instrument debtor creditor +
        if obligation.content.instrument = instrument ∧ obligation.content.debtor = debtor then
          shareAt input (boundary.event.after input) creditor else 0 := by
  unfold ledgerClaims
  change ((state.current.slots.set index (boundaryDisposition input boundary).targetSlot).map _).sum = _
  rw [List.map_set, List.sum_set']
  simp only [List.length_map, index.isLt, ↓reduceDIte, List.getElem_map]
  have row : state.current.slots[index.val] = .live obligation := present
  rw [row]
  have changed : slotClaims input (boundaryDisposition input boundary).targetSlot instrument debtor creditor =
      if obligation.content.instrument = instrument ∧ obligation.content.debtor = debtor then
        shareAt input (boundary.event.after input) creditor else 0 := by
    unfold slotClaims
    rw [boundary_claim, boundary_balance]
  rw [changed]
  ring

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
