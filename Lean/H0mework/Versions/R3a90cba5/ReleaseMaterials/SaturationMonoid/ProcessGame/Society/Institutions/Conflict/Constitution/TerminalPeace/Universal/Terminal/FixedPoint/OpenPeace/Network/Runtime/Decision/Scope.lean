import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Continuation
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (inspectList)
open Capitalism.Universal.Abolition.Material.Migration (sourceAlphabet)
open NoFreeProbe (PaidReview)

abbrev Checked (p : Prop) := Option (Decidable p)

namespace Checked

def map {p q : Prop} (equiv : p ↔ q) (checked : Checked p) : Checked q :=
  Option.map (fun
    | .isTrue present => .isTrue (equiv.mp present)
    | .isFalse absent => .isFalse (fun h => absent (equiv.mpr h))) checked

def or {p q : Prop} : Checked p → Checked q → Checked (p ∨ q)
  | some (.isTrue left), _ => some (.isTrue (.inl left))
  | _, some (.isTrue right) => some (.isTrue (.inr right))
  | some (.isFalse left), some (.isFalse right) =>
      some (.isFalse (fun h => h.elim left right))
  | _, _ => none


theorem map_complete {p q : Prop} (equiv : p ↔ q) {checked : Checked p}
    (complete : checked.isSome = true) : (map equiv checked).isSome = true := by
  cases checked <;> simp_all [map]

theorem or_complete {p q : Prop} {left : Checked p} {right : Checked q}
    (leftComplete : left.isSome = true) (rightComplete : right.isSome = true) :
    (or left right).isSome = true := by
  cases left with
  | none => simp at leftComplete
  | some left =>
    cases right with
    | none => simp at rightComplete
    | some right => cases left <;> cases right <;> rfl

theorem exactTrue {p : Prop} (checked : Checked p) (complete : checked.isSome = true)
    (actual : p) : checked = some (.isTrue actual) := by
  cases checked with
  | none => simp at complete
  | some decision =>
    cases decision with
    | isTrue _ => rfl
    | isFalse denied => exact (denied actual).elim

theorem exactFalse {p : Prop} (checked : Checked p) (complete : checked.isSome = true)
    (actual : ¬ p) : checked = some (.isFalse actual) := by
  cases checked with
  | none => simp at complete
  | some decision =>
    cases decision with
    | isFalse _ => rfl
    | isTrue found => exact (actual found).elim

end Checked

abbrev ReadSet {α : Type} (set : Set α) := ∀ point, Checked (point ∈ set)

def readEmpty {α : Type} : ReadSet (∅ : Set α) :=
  fun _ => some (.isFalse (fun h => h))

def readUnion {α : Type} {left right : Set α} (a : ReadSet left) (b : ReadSet right) :
    ReadSet (left ∪ right) :=
  fun point => Checked.or (a point) (b point)

def Language.readInitial {Old Point : Type} :
    ReadSet ((Language.initial : Language Old Point).covered) :=
  fun point => Checked.map (by rw [Language.covered_initial]) (readEmpty point)

/-- The language grows by the complete paid scope. The point reader uses
that same union and never adds a separate refusal registry. -/
def Language.readRepair {Old Point : Type} {old : Language Old Point} {observed : Set Point}
    (earlier : ReadSet old.covered) (actual : ReadSet observed) :
    ReadSet (old.repair observed).covered :=
  fun point => Checked.map (by rw [Language.covered_repair]) (readUnion earlier actual point)

variable {Party Good Port Technology Instrument : Type}

local notation "Prog" => ProgrammeSource.Input Party Good Port Technology Instrument

/-- Material technique and local registrations have no protected term
of their own. A differing projection of these normalized terms is an
exact witness against the proposed programme. -/
def inheritedTerms (old proposal : Prog) : Prog :=
  { old with law := { old.law with technique := proposal.law.technique }
             localAttempts := proposal.localAttempts }

def checkTermField {α : Type} [DecidableEq α] (old proposal : Prog) (read : Prog → α) :
    Checked (¬ KeepsPublicTerms old proposal) :=
  if different : read proposal ≠ read (inheritedTerms old proposal) then
    some (.isTrue (fun kept => different (congrArg read kept)))
  else none

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq (Request Party Good Port Technology Instrument)]

/-- Probe exact finite protected coordinates. An observed agreement
cannot assert equality of arbitrary policy functions. -/
def checkTerms (old proposal : Prog) : Checked (¬ KeepsPublicTerms old proposal) :=
  (checkTermField old proposal (fun p => p.initial.clock)).orElse fun _ =>
    (checkTermField old proposal (fun p => p.initial.round)).orElse fun _ =>
      checkTermField old proposal (fun p => p.instructions)

def checkAlphabet (old proposal : Prog)
    (before : RawCurrent Party Good Technology Instrument) :
    Decidable (∀ request ∈ sourceAlphabet old before, request ∈ sourceAlphabet proposal before) :=
  match inspectList (fun request => request ∈ sourceAlphabet proposal before) (sourceAlphabet old before) with
  | .clear kept => .isTrue kept
  | .failure request old absent => .isFalse (fun kept => absent (kept request old))

variable {Community : Type} [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}
  {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
  {bid : ReviewBid Party Good Port Technology Instrument}

/-- Any finite continuation can be checked on both sides of the actual
paid before-state. Protected terms use a separate exact comparison. -/
def readPaidScope (paid : PaidReview current bid) (proposal : Prog)
    (terms : Checked (¬ KeepsPublicTerms current.programme proposal)) :
    ReadSet (paidEffects paid proposal)
  | .inl claim =>
      some (lossDecision origin paid.round.visit.read.before.raw paid.round.visit.read.programme claim proposal)
  | .inr ⟨⟩ => Checked.map (paidEffects_public_terms paid proposal).symm terms

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
