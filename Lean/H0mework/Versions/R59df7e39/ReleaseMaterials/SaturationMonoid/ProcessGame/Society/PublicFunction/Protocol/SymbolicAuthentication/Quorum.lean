import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication
import Mathlib.Data.Fintype.Card

/-! Accountable quorum readouts. Exposure is computed from conflicting source
receipts, not a partition of actors into intrinsically good and bad nodes.
These finite readouts carry no authority or termination constructor. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Quorum

open Distributed

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

def support (state : ReceiverState code) (scope : Scope) (value : Fin code.signals) : Finset (Fin code.sites) :=
  ((state.receipts.filter fun receipt => decide (receipt.wire.scope = scope ∧ receipt.wire.payload = value)).map
    fun receipt => receipt.wire.key).toFinset

theorem mem_support_iff (state : ReceiverState code) (scope : Scope) (value : Fin code.signals)
    (key : Fin code.sites) : key ∈ support code state scope value ↔
    ∃ receipt ∈ state.receipts, receipt.wire.scope = scope ∧ receipt.wire.payload = value ∧ receipt.wire.key = key := by
  simp only [support, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨receipt, ⟨present, scope_eq, payload⟩, key_eq⟩
    exact ⟨receipt, present, scope_eq, payload, key_eq⟩
  · rintro ⟨receipt, present, scope_eq, payload, key_eq⟩
    exact ⟨receipt, ⟨present, scope_eq, payload⟩, key_eq⟩

def merged (left right : ReceiverState code) : ReceiverState code :=
  ⟨left.receipts ++ right.receipts, left.audit ++ right.audit⟩

def affected (left right : ReceiverState code) : Finset (Fin code.sites) :=
  ((evidence code (merged code left right)).map fun pair => pair.1.wire.key).toFinset

theorem conflicting_intersection_is_accounted (left right : ReceiverState code)
    (scope : Scope) (a b : Fin code.signals) (different : a ≠ b) :
    support code left scope a ∩ support code right scope b ⊆ affected code left right := by
  intro key inside
  obtain ⟨one, old, scope₁, value₁, key₁⟩ :=
    (mem_support_iff code left scope a key).mp (Finset.mem_inter.mp inside).1
  obtain ⟨two, new, scope₂, value₂, key₂⟩ :=
    (mem_support_iff code right scope b key).mp (Finset.mem_inter.mp inside).2
  have conflict : Conflicts code one.wire two.wire := by
    refine ⟨key₁.trans key₂.symm, scope₁.trans scope₂.symm, ?_⟩
    intro same
    exact different (value₁.symm.trans (same.trans value₂))
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(one, two), ?_, key₁⟩
  exact (evidence_iff code _ one two).mpr
    ⟨List.mem_append_left _ old, List.mem_append_right _ new, conflict⟩

inductive ReadoutData (Value : Type) where
  | blocked
  | decided (value : Value)
  deriving DecidableEq

abbrev Readout := ReadoutData (Fin code.signals)

def readout (state : ReceiverState code) (scope : Scope) (threshold : Nat) : Readout code :=
  if threshold = 0 then .blocked else
  match (List.finRange code.signals).find? (fun value => decide (threshold ≤ (support code state scope value).card)) with
  | none => .blocked
  | some value => .decided value

theorem decided_has_quorum (state : ReceiverState code) (scope : Scope) (threshold : Nat)
    (value : Fin code.signals) (decided : readout code state scope threshold = .decided value) :
    0 < threshold ∧ threshold ≤ (support code state scope value).card := by
  unfold readout at decided
  split at decided
  · contradiction
  · rename_i positive
    split at decided
    · contradiction
    · rename_i found result
      have same := ReadoutData.decided.inj decided
      subst found
      have enough := List.find?_some
        (p := fun v => decide (threshold ≤ (support code state scope v).card)) result
      exact ⟨Nat.pos_of_ne_zero positive, of_decide_eq_true enough⟩

/-- Agreement is conditional on an explicit, computed exposure bound. The
affected keys are obtained from the joint receipt history itself. -/
theorem agreement_of_generated_exposure_bound (left right : ReceiverState code)
    (scope : Scope) (threshold : Nat) (a b : Fin code.signals)
    (one : readout code left scope threshold = .decided a)
    (two : readout code right scope threshold = .decided b)
    (budget : code.sites + (affected code left right).card < threshold + threshold) : a = b := by
  by_contra different
  have first := (decided_has_quorum code left scope threshold a one).2
  have second := (decided_has_quorum code right scope threshold b two).2
  have exposed := Finset.card_le_card (conflicting_intersection_is_accounted code left right scope a b different)
  have union_bound : (support code left scope a ∪ support code right scope b).card ≤ code.sites := by
    simpa only [Fintype.card_fin] using (support code left scope a ∪ support code right scope b).card_le_univ
  have count := Finset.card_union_add_card_inter (support code left scope a) (support code right scope b)
  omega

theorem merged_generated_evidence_is_authenticated
    (interface : Interface code) (policy : code.Policy)
    (initial : Institutions.Capitalism.Universal.Source.Program.RawCurrent Party Good Technology Instrument)
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (leftSite rightSite : Fin code.sites) (leftInput rightInput : Nat → Option (Envelope code))
    (leftCount rightCount : Nat) (one two : Receipt code)
    (present : (one, two) ∈ evidence code (merged code
      (run code interface policy initial events leftSite leftInput leftCount)
      (run code interface policy initial events rightSite rightInput rightCount))) :
    verify code interface policy initial events one.wire = true ∧
      verify code interface policy initial events two.wire = true ∧
      one.wire.occurrence ≠ two.wire.occurrence ∧ Conflicts code one.wire two.wire := by
  obtain ⟨first, second, conflict⟩ := (evidence_iff code _ one two).mp present
  have auth : ∀ receipt ∈ (merged code
      (run code interface policy initial events leftSite leftInput leftCount)
      (run code interface policy initial events rightSite rightInput rightCount)).receipts,
      verify code interface policy initial events receipt.wire = true := by
    intro receipt member
    rcases List.mem_append.mp member with left | right
    · exact (receipts_authenticated code interface policy initial events leftSite leftInput leftCount receipt left).1
    · exact (receipts_authenticated code interface policy initial events rightSite rightInput rightCount receipt right).1
  have auth₁ := auth one first
  have auth₂ := auth two second
  refine ⟨auth₁, auth₂, ?_, conflict⟩
  intro same
  exact conflict.2.2 (congrArg EnvelopeData.payload
    (same_symbol_same_message code interface policy initial events one.wire two.wire auth₁ auth₂ same))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Quorum
