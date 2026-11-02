import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Finance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling

open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

inductive ListComparison {α : Type} (first second : List α) where
  | equal (same : second = first)
  | different (index : Nat) (mismatch : second[index]? ≠ first[index]?)

def compareLists {α : Type} [DecidableEq α] : (first second : List α) → ListComparison first second
  | [], [] => .equal rfl
  | [], _ :: _ => .different 0 (by simp)
  | _ :: _, [] => .different 0 (by simp)
  | first :: rest, second :: tail =>
      if same : second = first then
        match compareLists rest tail with
        | .equal lists => .equal (by rw [same, lists])
        | .different index mismatch => .different (index + 1) (by simpa using mismatch)
      else .different 0 (by simpa using same)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)
  (original replacement : ProgrammeSource.Input Party Good Port Technology Instrument)
  (old : (Financial.process original).GeneratedState)
  (new : (Financial.process replacement).GeneratedState)

structure RecordImage (Party Good Port Technology Instrument : Type) where
  slot : Nat
  kind : LifecycleKind
  before : Option (Identity.DebtImage Party Good Port Technology Instrument)
  after : Identity.DebtImage Party Good Port Technology Instrument
  source : Identity.EventImage Party Good Port Technology Instrument
  deriving DecidableEq

def recordImage (input : ProgrammeSource.Input Party Good Port Technology Instrument) :
    LifecycleEvent (Financial.vocabulary input) → RecordImage Party Good Port Technology Instrument
  | .admitted slot payload =>
      ⟨slot, .admitted, none, Identity.debtImage code input (.live payload.toObligation),
        Identity.eventImage code input payload.sourceEvent⟩
  | .carried slot obligation source carry =>
      ⟨slot, (LifecycleEvent.carried slot obligation source carry).kind,
        some (Identity.debtImage code input (.live obligation)),
        Identity.debtImage code input (BoundaryDisposition.carry carry).targetSlot,
        Identity.eventImage code input source⟩
  | .terminal slot obligation source receipt =>
      ⟨slot, .obligationTerminal, some (Identity.debtImage code input (.live obligation)),
        Identity.debtImage code input (BoundaryDisposition.terminal (.final receipt)).targetSlot,
        Identity.eventImage code input source⟩
  | .superseded slot obligation source receipt =>
      ⟨slot, .superseded, some (Identity.debtImage code input (.live obligation)),
        Identity.debtImage code input (BoundaryDisposition.terminal (.superseded receipt)).targetSlot,
        Identity.eventImage code input source⟩
  | .bearerReleased slot obligation source receipt =>
      ⟨slot, .bearerRelease, some (Identity.debtImage code input (.live obligation)),
        Identity.debtImage code input (BoundaryDisposition.bearerRelease receipt).targetSlot,
        Identity.eventImage code input source⟩
  | .reopened slot archive payload =>
      ⟨slot, .reopened, some (Identity.debtImage code input (.terminal archive)),
        Identity.debtImage code input (.live payload.admission.toObligation),
        Identity.eventImage code input payload.sourceEvent⟩

def eventHistory (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (state : (Financial.process input).GeneratedState) :=
  state.current.history.map (recordImage code input)

structure RecordCorrespondence
    (old : LifecycleEvent (Financial.vocabulary original))
    (new : LifecycleEvent (Financial.vocabulary replacement)) : Prop where
  image : recordImage code replacement new = recordImage code original old

structure Match : Prop where
  slots : Identity.financeImage code replacement new = Identity.financeImage code original old
  events : eventHistory code replacement new = eventHistory code original old

inductive Mismatch where
  | debt (index : Nat) (different :
      (Identity.financeImage code replacement new)[index]? ≠ (Identity.financeImage code original old)[index]?)
  | event (index : Nat) (different :
      (eventHistory code replacement new)[index]? ≠ (eventHistory code original old)[index]?)

inductive Outcome where
  | matched (transport : Match code original replacement old new)
  | mismatch (witness : Mismatch code original replacement old new)

def generate : Outcome code original replacement old new :=
  match compareLists (Identity.financeImage code original old) (Identity.financeImage code replacement new) with
  | .different index different => .mismatch (.debt index different)
  | .equal slots =>
      match compareLists (eventHistory code original old) (eventHistory code replacement new) with
      | .different index different => .mismatch (.event index different)
      | .equal events => .matched ⟨slots, events⟩

def Outcome.accepted : Outcome code original replacement old new → Bool
  | .matched _ => true
  | .mismatch _ => false

def Outcome.discrepancy : Outcome code original replacement old new → Option (Nat ⊕ Nat)
  | .matched _ => none
  | .mismatch (.debt index _) => some (.inl index)
  | .mismatch (.event index _) => some (.inr index)

def verify : Bool := decide
  (Identity.financeImage code replacement new = Identity.financeImage code original old ∧
    eventHistory code replacement new = eventHistory code original old)

theorem verify_iff : verify code original replacement old new = true ↔ Match code original replacement old new := by
  simp only [verify, decide_eq_true_eq]
  exact ⟨fun same => ⟨same.1, same.2⟩, fun same => ⟨same.slots, same.events⟩⟩


namespace Match

variable {code original replacement old new}
  (matched : Match code original replacement old new)

include matched

omit [DecidableEq Technology] in
theorem every_original_slot_has_its_own_replacement :
    ∀ index (inside : index < old.current.slots.length),
      ∃ slot ∈ new.current.slots,
        Identity.DebtCorrespondence code original replacement old.current.slots[index] slot :=
  Identity.equal_images_recover_each_original_native_debt code original replacement old new matched.slots

omit [DecidableEq Technology] in
theorem every_replacement_slot_has_its_own_original :
    ∀ index (inside : index < new.current.slots.length),
      ∃ slot ∈ old.current.slots,
        Identity.DebtCorrespondence code replacement original new.current.slots[index] slot :=
  Identity.equal_images_recover_each_original_native_debt code replacement original new old matched.slots.symm

omit [DecidableEq Technology] in
theorem every_original_record_has_its_own_replacement :
    ∀ index (inside : index < old.current.history.length),
      ∃ record ∈ new.current.history,
        RecordCorrespondence code original replacement old.current.history[index] record := by
  intro index inside
  have lengths := congrArg List.length matched.events
  simp only [eventHistory, List.length_map] at lengths
  have bounded : index < new.current.history.length := by omega
  refine ⟨new.current.history[index], List.getElem_mem bounded, ?_⟩
  constructor
  have row := congrArg (fun rows => rows[index]?) matched.events
  change (new.current.history.map (recordImage code replacement))[index]? =
    (old.current.history.map (recordImage code original))[index]? at row
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem bounded, List.getElem?_eq_getElem inside] at row
  exact Option.some.inj row

omit [DecidableEq Technology] in
theorem every_replacement_record_has_its_own_original :
    ∀ index (inside : index < new.current.history.length),
      ∃ record ∈ old.current.history,
        RecordCorrespondence code replacement original new.current.history[index] record := by
  intro index inside
  have lengths := congrArg List.length matched.events
  simp only [eventHistory, List.length_map] at lengths
  have bounded : index < old.current.history.length := by omega
  refine ⟨old.current.history[index], List.getElem_mem bounded, ?_⟩
  constructor
  have row := congrArg (fun rows => rows[index]?) matched.events.symm
  change (old.current.history.map (recordImage code original))[index]? =
    (new.current.history.map (recordImage code replacement))[index]? at row
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem bounded, List.getElem?_eq_getElem inside] at row
  exact Option.some.inj row

private def claimsFromImage (image : Identity.DebtImage Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  if image.claim.instrument = instrument ∧ image.claim.debtor = debtor then image.balance creditor else 0

omit [DecidableEq Technology] in
theorem same_native_quota (instrument : Instrument) (debtor creditor : Party) :
    Financial.BalanceConservation.ledgerClaims replacement new.current instrument debtor creditor =
      Financial.BalanceConservation.ledgerClaims original old.current instrument debtor creditor := by
  have same := congrArg (fun images => (images.map (fun image => claimsFromImage image instrument debtor creditor)).sum)
    matched.slots
  have read (input : ProgrammeSource.Input Party Good Port Technology Instrument)
      (slot : ObligationSlot (Financial.vocabulary input)) :
      claimsFromImage (Identity.debtImage code input slot) instrument debtor creditor =
        Financial.BalanceConservation.slotClaims input slot instrument debtor creditor := by
    simp [claimsFromImage, Identity.debtImage, Identity.claimImage,
      Financial.BalanceConservation.slotClaims, Financial.BalanceConservation.shareAt, Financial.slotClaim]
    split_ifs <;> rfl
  simpa only [Identity.financeImage, List.map_map, Function.comp_def, read,
    Financial.BalanceConservation.ledgerClaims] using same


omit [DecidableEq Technology] in
theorem excludes_every_concrete_mismatch (witness : Mismatch code original replacement old new) : False := by
  cases witness with
  | debt index different => exact different (congrArg (fun rows => rows[index]?) matched.slots)
  | event index different => exact different (congrArg (fun rows => rows[index]?) matched.events)

end Match

theorem generated_transport_iff :
    (generate code original replacement old new).accepted = true ↔ Match code original replacement old new := by
  cases produced : generate code original replacement old new with
  | matched transport => exact ⟨fun _ => transport, fun _ => rfl⟩
  | mismatch witness =>
      constructor
      · intro impossible
        cases impossible
      · intro matched
        exact False.elim (matched.excludes_every_concrete_mismatch witness)


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling
