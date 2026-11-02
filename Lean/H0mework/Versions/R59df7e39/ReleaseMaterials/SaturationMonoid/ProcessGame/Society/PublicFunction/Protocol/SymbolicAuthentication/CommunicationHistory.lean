import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationDuty

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationDuty

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

inductive Shape (emission : Emission source input cut protocol rival vocabulary encoding)
    (steps : Nat) (state : ResponsibilityState (V source input cut protocol rival vocabulary encoding law)) : Type
  | live (unconfirmed : ∀ k < steps,
        ¬ Acknowledged source input cut protocol rival vocabulary encoding law emission (emission.send + 1 + k))
      (slots : state.slots = [.live (obligation source input cut protocol rival vocabulary encoding law emission)])
  | terminal (first : Nat) (earlier : first < steps)
      (ack : Acknowledged source input cut protocol rival vocabulary encoding law emission (emission.send + 1 + first))
      (slots : state.slots = [.terminal (archive source input cut protocol rival vocabulary encoding law emission
        (emission.send + 1 + first) ack)])

structure Prefix (emission : Emission source input cut protocol rival vocabulary encoding) (steps : Nat) where
  state : ResponsibilityState (V source input cut protocol rival vocabulary encoding law)
  run : (process source input cut protocol rival vocabulary encoding law).Run
    (ResponsibilityState.empty (V source input cut protocol rival vocabulary encoding law)) state
  shape : Shape source input cut protocol rival vocabulary encoding law emission steps state

def initial (emission : Emission source input cut protocol rival vocabulary encoding) :
    Prefix source input cut protocol rival vocabulary encoding law emission 0 :=
  let edge : (process source input cut protocol rival vocabulary encoding law).Edge
      (ResponsibilityState.empty (V source input cut protocol rival vocabulary encoding law)) := .admit emission
  ⟨edge.target, .step .nil edge, .live (by intro k impossible; omega) rfl⟩

def advance (emission : Emission source input cut protocol rival vocabulary encoding) (steps : Nat)
    (prior : Prefix source input cut protocol rival vocabulary encoding law emission steps) :
    Prefix source input cut protocol rival vocabulary encoding law emission (steps + 1) := by
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unconfirmed slots =>
    let address : Fin state.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
    have present : state.slots.get address =
        .live (obligation source input cut protocol rival vocabulary encoding law emission) := by simp [slots, address]
    let edge : (process source input cut protocol rival vocabulary encoding law).Edge state :=
      .cross address _ present (review source input cut protocol rival vocabulary encoding law emission (emission.send + 1 + steps))
    by_cases ack : Acknowledged source input cut protocol rival vocabulary encoding law emission (emission.send + 1 + steps)
    · exact ⟨edge.target, .step run edge, .terminal steps (by omega) ack (by
        simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource,
          review, dif_pos ack, slots, address, BoundaryDisposition.targetSlot, archive])⟩
    · exact ⟨edge.target, .step run edge, .live (by
        intro k bound
        by_cases old : k < steps
        · exact unconfirmed k old
        · have same : k = steps := by omega
          exact same ▸ ack) (by
        simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource,
          review, dif_neg ack, slots, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])⟩
  | terminal first earlier ack slots => exact ⟨state, run, .terminal first (by omega) ack slots⟩

def through (emission : Emission source input cut protocol rival vocabulary encoding) :
    (steps : Nat) → Prefix source input cut protocol rival vocabulary encoding law emission steps
  | 0 => initial source input cut protocol rival vocabulary encoding law emission
  | steps + 1 => advance source input cut protocol rival vocabulary encoding law emission steps (through emission steps)

theorem terminal_iff_actual_content_receipt
    (emission : Emission source input cut protocol rival vocabulary encoding) (horizon : Nat)
    (inside : emission.send < horizon) :
    (through source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)).state.TerminalAt 0 ↔
      Acknowledged source input cut protocol rival vocabulary encoding law emission horizon := by
  cases (through source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)).shape with
  | live unconfirmed slots =>
    constructor
    · rintro ⟨old, impossible⟩; simp [slots] at impossible
    · intro ack
      have missing := unconfirmed (horizon - emission.send - 1) (by omega)
      have last : emission.send + 1 + (horizon - emission.send - 1) = horizon := by omega
      exact False.elim (missing (last.symm ▸ ack))
  | terminal first earlier ack slots =>
    exact ⟨fun _ => acknowledged_is_preserved source input cut protocol rival vocabulary encoding law emission
      (emission.send + 1 + first) horizon (by omega) ack,
      fun _ => ⟨archive source input cut protocol rival vocabulary encoding law emission
        (emission.send + 1 + first) ack, by simp [slots]⟩⟩

theorem live_iff_no_content_receipt
    (emission : Emission source input cut protocol rival vocabulary encoding) (horizon : Nat)
    (inside : emission.send < horizon) :
    (through source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)).state.LiveAt 0 ↔
      ¬ Acknowledged source input cut protocol rival vocabulary encoding law emission horizon := by
  cases (through source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)).shape with
  | live unconfirmed slots =>
    constructor
    · intro _ ack
      have missing := unconfirmed (horizon - emission.send - 1) (by omega)
      have last : emission.send + 1 + (horizon - emission.send - 1) = horizon := by omega
      exact missing (last.symm ▸ ack)
    · intro _; exact ⟨obligation source input cut protocol rival vocabulary encoding law emission, by simp [slots]⟩
  | terminal first earlier ack slots =>
    constructor
    · rintro ⟨old, impossible⟩; simp [slots] at impossible
    · intro missing
      exact False.elim (missing (acknowledged_is_preserved source input cut protocol rival vocabulary encoding law emission
        (emission.send + 1 + first) horizon (by omega) ack))

theorem original_admission_and_complete_native_history
    (emission : Emission source input cut protocol rival vocabulary encoding) (steps : Nat) :
    (through source input cut protocol rival vocabulary encoding law emission steps).state.history =
        (through source input cut protocol rival vocabulary encoding law emission steps).run.events ∧
      (through source input cut protocol rival vocabulary encoding law emission steps).state.slots.length = 1 ∧
      (∀ record, (through source input cut protocol rival vocabulary encoding law emission steps).state.slots[0]? =
        some (.terminal record) → record.obligation = obligation source input cut protocol rival vocabulary encoding law emission) := by
  refine ⟨by simpa [ResponsibilityState.empty] using
    (through source input cut protocol rival vocabulary encoding law emission steps).run.history_eq, ?_⟩
  cases (through source input cut protocol rival vocabulary encoding law emission steps).shape with
  | live unconfirmed slots =>
    refine ⟨by simp [slots], ?_⟩
    intro record impossible
    simp [slots] at impossible
  | terminal first earlier ack slots =>
    refine ⟨by simp [slots], ?_⟩
    intro record present
    have same : archive source input cut protocol rival vocabulary encoding law emission
        (emission.send + 1 + first) ack = record := by simpa [slots] using present
    exact same ▸ rfl

theorem first_archive_is_retained
    (emission : Emission source input cut protocol rival vocabulary encoding) (steps later : Nat)
    (terminal : (through source input cut protocol rival vocabulary encoding law emission steps).state.TerminalAt 0) :
    (through source input cut protocol rival vocabulary encoding law emission (steps + later)).state =
      (through source input cut protocol rival vocabulary encoding law emission steps).state := by
  induction later with
  | zero => rfl
  | succ later ih =>
    have still : (through source input cut protocol rival vocabulary encoding law emission (steps + later)).state.TerminalAt 0 :=
      ih ▸ terminal
    change (advance source input cut protocol rival vocabulary encoding law emission (steps + later)
      (through source input cut protocol rival vocabulary encoding law emission (steps + later))).state = _
    generalize through source input cut protocol rival vocabulary encoding law emission (steps + later) = prior at *
    rcases prior with ⟨state, run, shape⟩
    cases shape with
    | live unconfirmed slots =>
      obtain ⟨record, present⟩ := still
      simp [slots] at present
    | terminal first earlier ack slots => exact ih

def histories (horizon : Nat) : List (Sigma fun emission : Emission source input cut protocol rival vocabulary encoding =>
    Prefix source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)) :=
  (origins source input cut protocol rival vocabulary encoding horizon).map fun emission =>
    ⟨emission, through source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)⟩

theorem expired_without_delivery_keeps_the_original_duty_live
    (emission : Emission source input cut protocol rival vocabulary encoding) (horizon : Nat)
    (inside : emission.send < horizon)
    (missed : AvailabilityAudit.classify source input cut protocol rival vocabulary encoding law
      emission.wire.recipient horizon emission.wire = .noDelivery) :
    (through source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)).state.LiveAt 0 := by
  apply (live_iff_no_content_receipt source input cut protocol rival vocabulary encoding law emission horizon inside).mpr
  obtain ⟨_, _, absent⟩ := AvailabilityAudit.no_delivery_has_expired_and_has_no_actual_attempt
    source input cut protocol rival vocabulary encoding law emission.wire.recipient horizon emission.wire missed
  rintro ⟨receipt, present, same⟩
  exact absent receipt present same

theorem every_first_paid_send_has_its_native_history (horizon n : Nat)
    (inside : n < horizon) (emission : Emission source input cut protocol rival vocabulary encoding)
    (born : birth source input cut protocol rival vocabulary encoding n = some emission) :
    (⟨emission, through source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)⟩ :
      Sigma fun emission : Emission source input cut protocol rival vocabulary encoding =>
        Prefix source input cut protocol rival vocabulary encoding law emission (horizon - emission.send)) ∈
      histories source input cut protocol rival vocabulary encoding law horizon :=
  List.mem_map.mpr ⟨emission, List.mem_filterMap.mpr ⟨n, List.mem_range.mpr inside, born⟩, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationDuty
