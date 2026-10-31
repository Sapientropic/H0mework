import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

/-- A finite execution trail, with no caller-supplied endpoint or payments.
Only the canonical restriction below is identified with a root occurrence. -/
inductive ExecutionPrefix (source : OutstandingSource Party Good Port Technology Instrument) where
  | start
  | extend (prior : ExecutionPrefix source) (word : RawEvent Party Good Port Technology Instrument)

namespace ExecutionPrefix

variable {source}

def empty (source : OutstandingSource Party Good Port Technology Instrument) : ExecutionPrefix source := .start
def append (prior : ExecutionPrefix source) (word : RawEvent Party Good Port Technology Instrument) :
    ExecutionPrefix source := .extend prior word

def length : ExecutionPrefix source → Nat
  | .start => 0
  | .extend prior _ => prior.length + 1

def frame : ExecutionPrefix source → source.Frame
  | .start => ⟨source.seed.initial, fun _ => none⟩
  | .extend prior word => ⟨source.seed.law.next prior.frame.raw word,
      source.update prior.frame.payments prior.frame.raw word prior.length⟩

def AllAccepted : ExecutionPrefix source → Prop
  | .start => True
  | .extend prior word => prior.AllAccepted ∧
      ∀ item ∈ source.seed.law.rawItems prior.frame.raw word,
        source.seed.law.Valid item.before item.request

inductive Occurred : ExecutionPrefix source → Nat →
    RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument → Prop
  | last (prior : ExecutionPrefix source) (word) :
      Occurred (prior.append word) prior.length prior.frame.raw word
  | earlier {prior : ExecutionPrefix source} {ordinal current word} (later)
      (occurred : Occurred prior ordinal current word) :
      Occurred (prior.append later) ordinal current word

theorem append_keeps_archive (prior : ExecutionPrefix source) (word) (index : source.Slot) (paid : Nat)
    (recorded : prior.frame.payments index = some paid) :
    (prior.append word).frame.payments index = some paid := by
  exact source.payment_preserved _ _ _ _ index paid recorded

theorem recorded_has_execution (prior : ExecutionPrefix source) (index : source.Slot) (paid : Nat)
    (recorded : prior.frame.payments index = some paid) :
    paid < prior.length ∧ ∃ current word, prior.Occurred paid current word ∧ source.SlotPaid current word index := by
  induction prior with
  | start => cases recorded
  | extend prior word ih =>
      change source.update prior.frame.payments prior.frame.raw word prior.length index = some paid at recorded
      unfold update at recorded
      split at recorded
      next old previous =>
        obtain ⟨before, current, original, occurred, actual⟩ := ih (previous.trans recorded)
        exact ⟨Nat.lt_succ_of_lt before, current, original, .earlier word occurred, actual⟩
      next =>
        split at recorded
        next actual =>
          have same : prior.length = paid := Option.some.inj recorded
          subst paid
          exact ⟨Nat.lt_succ_self _, prior.frame.raw, word, .last prior word, actual⟩
        next => cases recorded

theorem unpaid_append_iff (prior : ExecutionPrefix source) (word) (index : source.Slot)
    (unpaid : prior.frame.payments index = none) :
    (prior.append word).frame.payments index = none ↔ ¬ source.SlotPaid prior.frame.raw word index := by
  change source.update _ _ _ _ index = none ↔ _
  simp only [update, unpaid, ite_eq_right_iff, reduceCtorEq, imp_false]

def respond (prior : ExecutionPrefix source) : ExecutionPrefix source :=
  prior.append (source.decideAt prior.frame.raw prior.frame.payments).word

def continueFrom (prior : ExecutionPrefix source) : Nat → ExecutionPrefix source
  | 0 => prior
  | rounds + 1 => (continueFrom prior rounds).respond

theorem continue_keeps_archive (prior : ExecutionPrefix source) (rounds : Nat)
    (index : source.Slot) (paid : Nat) (recorded : prior.frame.payments index = some paid) :
    (prior.continueFrom rounds).frame.payments index = some paid := by
  induction rounds with
  | zero => exact recorded
  | succ rounds ih => exact append_keeps_archive _ _ index paid ih

end ExecutionPrefix

/-- All finite RawLaw-legal word paths, without a word-budget restriction. -/
def RawLegalReach (current : RawCurrent Party Good Technology Instrument) : Prop :=
  ∃ trail : ExecutionPrefix source, trail.AllAccepted ∧ trail.frame.raw = current

theorem legal_reach_initial : source.RawLegalReach source.seed.initial :=
  ⟨ExecutionPrefix.empty source, trivial, rfl⟩

theorem legal_reach_next (current) (reached : source.RawLegalReach current) (word)
    (accepted : ∀ item ∈ source.seed.law.rawItems current word,
      source.seed.law.Valid item.before item.request) :
    source.RawLegalReach (source.seed.law.next current word) := by
  obtain ⟨trail, legal, same⟩ := reached
  exact ⟨trail.append word, ⟨legal, same ▸ accepted⟩, congrArg (fun raw => source.seed.law.next raw word) same⟩

def canonicalPrefix : Nat → ExecutionPrefix source
  | 0 => .empty source
  | ordinal + 1 => (canonicalPrefix ordinal).append (source.frameWord ordinal (source.frameAt ordinal))

theorem canonical_trail_exact (ordinal : Nat) :
    (source.canonicalPrefix ordinal).length = ordinal ∧
    (source.canonicalPrefix ordinal).frame = source.frameAt ordinal := by
  induction ordinal with
  | zero => exact ⟨rfl, rfl⟩
  | succ ordinal ih =>
      constructor
      · exact congrArg Nat.succ ih.1
      · change (⟨source.seed.law.next _ _, source.update _ _ _ _⟩ : source.Frame) = _
        rw [ih.1, ih.2]
        rfl

theorem canonical_respond (ordinal : Nat) (started : 2 ≤ ordinal) :
    (source.canonicalPrefix ordinal).respond = source.canonicalPrefix (ordinal + 1) := by
  change (source.canonicalPrefix ordinal).append
    (source.decideAt (source.canonicalPrefix ordinal).frame.raw (source.canonicalPrefix ordinal).frame.payments).word =
      (source.canonicalPrefix ordinal).append (source.frameWord ordinal (source.frameAt ordinal))
  congr 1
  rw [(source.canonical_trail_exact ordinal).2]
  unfold frameWord
  rw [if_neg (by omega), if_neg (by omega)]

theorem canonical_continuation (ordinal rounds : Nat) (started : 2 ≤ ordinal) :
    (source.canonicalPrefix ordinal).continueFrom rounds = source.canonicalPrefix (ordinal + rounds) := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      change ((source.canonicalPrefix ordinal).continueFrom rounds).respond = _
      rw [ih, source.canonical_respond (ordinal + rounds) (by omega)]
      rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource
