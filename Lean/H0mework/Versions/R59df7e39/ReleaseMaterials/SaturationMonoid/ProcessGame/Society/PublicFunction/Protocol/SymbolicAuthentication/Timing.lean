import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceExposure

/-! Finite timing dispositions use actual source-event cuts, not wall time.
An absent future event cannot advance a deadline. Expiry records missing
accepted communication; it does not identify who caused the omission. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Timing

open Distributed Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

inductive StatusData (Wire : Type) where
  | notEmitted
  | awaiting (deadline : Nat)
  | onTime (receipt : ReceiptData Wire)
  | late (receipt : ReceiptData Wire)
  | expired (audit : List (EntryData Wire))
  deriving DecidableEq

abbrev Status := StatusData (Envelope code)

variable (interface : Interface code) (policy : code.Policy)
  (initial : RawCurrent Party Good Technology Instrument)

def status (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (delay horizon emission : Nat) : Status code :=
  let cut := min horizon events.length
  match issuedAt code interface policy initial (events.take cut) emission with
  | none => .notEmitted
  | some _ =>
      let state := run code interface policy initial events receiver incoming cut
      match state.receipts.find? (fun receipt => receipt.wire.occurrence == emission) with
      | some receipt => if receipt.delivery ≤ emission + delay then .onTime receipt else .late receipt
      | none => if cut ≤ emission + delay then .awaiting (emission + delay) else .expired state.audit

theorem on_time_is_actual_authenticated_delivery
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (delay horizon emission : Nat) (receipt : Receipt code)
    (successful : status code interface policy initial events receiver incoming delay horizon emission = .onTime receipt) :
    verify code interface policy initial events receipt.wire = true ∧
      receipt.wire.recipient = receiver ∧ receipt.wire.occurrence < receipt.delivery ∧
      receipt.delivery < min horizon events.length ∧
      deliveredAt code events receipt.delivery receipt.wire.serial = true ∧
      receipt.wire.occurrence = emission ∧ receipt.delivery ≤ emission + delay := by
  cases issued : issuedAt code interface policy initial (events.take (min horizon events.length)) emission with
  | none =>
    simp only [status, issued] at successful
    cases successful
  | some wire =>
    cases found : (run code interface policy initial events receiver incoming (min horizon events.length)).receipts.find?
        (fun receipt => receipt.wire.occurrence == emission) with
    | none =>
      simp only [status, issued, found] at successful
      split_ifs at successful
    | some result =>
      simp only [status, issued, found] at successful
      by_cases timely : result.delivery ≤ emission + delay
      · rw [if_pos timely] at successful
        have same := StatusData.onTime.inj successful
        subst receipt
        have member := List.mem_of_find?_eq_some found
        have origin := receipts_authenticated code interface policy initial events receiver incoming
          (min horizon events.length) result member
        have symbol := List.find?_some
          (p := fun receipt : Receipt code => receipt.wire.occurrence == emission) found
        exact ⟨origin.1, origin.2.1, origin.2.2.1, origin.2.2.2.1, origin.2.2.2.2,
          beq_iff_eq.mp symbol, timely⟩
      · rw [if_neg timely] at successful
        contradiction

theorem expiry_has_no_accepted_receipt
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (delay horizon emission : Nat) (audit : List (Entry code))
    (expired : status code interface policy initial events receiver incoming delay horizon emission = .expired audit) :
    emission + delay < min horizon events.length ∧
      audit = (run code interface policy initial events receiver incoming (min horizon events.length)).audit ∧
      ∀ receipt ∈ (run code interface policy initial events receiver incoming (min horizon events.length)).receipts,
        receipt.wire.occurrence ≠ emission := by
  cases issued : issuedAt code interface policy initial (events.take (min horizon events.length)) emission with
  | none =>
    simp only [status, issued] at expired
    cases expired
  | some wire =>
    cases found : (run code interface policy initial events receiver incoming (min horizon events.length)).receipts.find?
        (fun receipt => receipt.wire.occurrence == emission) with
    | some result =>
      simp only [status, issued, found] at expired
      split_ifs at expired
    | none =>
      simp only [status, issued, found] at expired
      by_cases waiting : min horizon events.length ≤ emission + delay
      · rw [if_pos waiting] at expired
        contradiction
      · rw [if_neg waiting] at expired
        refine ⟨by omega, (StatusData.expired.inj expired).symm, ?_⟩
        intro receipt member same
        have never := List.find?_eq_none.mp found receipt member
        simp only [same, beq_self_eq_true] at never
        contradiction

theorem agreement_across_actual_cuts
    (ports : Fin code.sites → Port)
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (leftSite rightSite : Fin code.sites) (leftInput rightInput : Nat → Option (Envelope code))
    (leftCount rightCount count threshold : Nat) (scope : Scope) (a b : Fin code.signals)
    (leftBound : leftCount ≤ count) (rightBound : rightCount ≤ count)
    (one : Quorum.readout code (run code interface policy initial events leftSite leftInput leftCount)
      scope threshold = .decided a)
    (two : Quorum.readout code (run code interface policy initial events rightSite rightInput rightCount)
      scope threshold = .decided b)
    (enough : code.sites + SourceExposure.budget code ports policy initial events count < threshold + threshold) : a = b := by
  have covered := Finset.card_le_card (SourceExposure.received_exposure_is_bounded_by_source code ports policy initial
    interface events leftSite rightSite leftInput rightInput leftCount rightCount count leftBound rightBound)
  apply Quorum.agreement_of_generated_exposure_bound code _ _ scope threshold a b one two
  exact lt_of_le_of_lt (Nat.add_le_add_left covered code.sites) enough

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Timing
