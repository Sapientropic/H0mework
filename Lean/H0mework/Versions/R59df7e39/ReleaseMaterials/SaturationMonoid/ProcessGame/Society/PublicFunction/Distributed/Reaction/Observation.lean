import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Compiler
import Mathlib.Data.List.Dedup

/-! The opponent sees its complete event history and actual protocol frame.
Its finite observation domain is generated before choosing a replacement,
from every source policy, legal history and supported event prefix. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction

open Institutions.Capitalism.Universal.Source.Program

deriving instance DecidableEq for Operation
deriving instance DecidableEq for Request
deriving instance DecidableEq for Event

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

instance packetDecidableEq : DecidableEq code.Packet := fun a b =>
  decidable_of_iff (a.sender = b.sender ∧ a.recipient = b.recipient ∧
    a.signal = b.signal ∧ a.sentAfter = b.sentAfter) (by cases a; cases b; simp)

instance frameDecidableEq : DecidableEq code.Frame := fun a b =>
  decidable_of_iff (a.word = b.word ∧ a.sent = b.sent ∧
    (∀ site, a.inbox site = b.inbox site) ∧ a.localLegal = b.localLegal) (by
      cases a; cases b
      simp only [Code.Frame.mk.injEq, funext_iff])

abbrev History := List (RawEvent Party Good Port Technology Instrument)
abbrev Events := List (Event Party Good Port Technology Instrument code.sites)
abbrev Choice := { event : Event Party Good Port Technology Instrument code.sites // event ∈ code.eventAlphabet }
abbrev Move := Option (Choice code)
abbrev Opponent := History (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument) → Events code → code.Frame → Move code
abbrev Key := History (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument) × Events code × code.Frame

instance keyDecidableEq : DecidableEq (Key code) := fun a b =>
  decidable_of_iff (a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2) (by
    simp only [Prod.ext_iff])

def keys : List (Key code) :=
  (code.histories.flatMap (fun history => code.policies.flatMap (fun policy =>
    ((sequences code.eventAlphabet code.eventLimit).filter (fun events => events.length < code.eventLimit)).map
      (fun events => (history, events, code.replay policy (code.historyCurrent history) events))))).dedup

theorem every_reachable_decision_is_a_key (policy : code.Policy) (generated : policy ∈ code.policies)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (original : history ∈ code.histories) (events : Events code)
    (bounded : events.length < code.eventLimit)
    (supported : ∀ event ∈ events, event ∈ code.eventAlphabet) :
    (history, events, code.replay policy (code.historyCurrent history) events) ∈ keys code := by
  unfold keys
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨history, original, List.mem_flatMap.mpr ⟨policy, generated, ?_⟩⟩
  exact List.mem_map.mpr ⟨events, List.mem_filter.mpr
    ⟨(mem_sequences_iff _ _ _).mpr ⟨Nat.le_of_lt bounded, supported⟩, by simpa using bounded⟩, rfl⟩

def moves : List (Move code) := none :: code.eventAlphabet.attach.map some

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_move_is_generated (move : Move code) : move ∈ moves code := by
  cases move with
  | none => exact List.mem_cons_self
  | some event => exact List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨event, List.mem_attach _ _, rfl⟩)

abbrev Table := ∀ key ∈ keys code, Move code

def tables : List (Table code) := List.pi (keys code) (fun _ => moves code)

def respond (table : Table code) (history : History (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (events : Events code) (frame : code.Frame) : Move code :=
  if original : (history, events, frame) ∈ keys code then table _ original else none

def restrict (opponent : Opponent code) : Table code := fun key _ => opponent key.1 key.2.1 key.2.2

theorem restriction_is_generated (opponent : Opponent code) : restrict code opponent ∈ tables code := by
  unfold tables
  apply (List.mem_pi _ _).mpr
  intro key _
  exact every_move_is_generated code _

theorem restriction_agrees_on_every_reachable_decision (opponent : Opponent code)
    (key : Key code) (original : key ∈ keys code) :
    respond code (restrict code opponent) key.1 key.2.1 key.2.2 = opponent key.1 key.2.1 key.2.2 := by
  simp only [respond, show (key.1, key.2.1, key.2.2) = key by cases key; rfl,
    dif_pos original, restrict]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction
