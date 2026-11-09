import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Service
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
open PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port))
  (current : RawCurrent Party Good (State Party Technology) Instrument) (first second : Party) (unit : Good)

local notation "Stamped" => PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] in
private theorem review_request_same (current : Raw) (signer : Party) {a b : ℚ}
    (early : a < current.clock) (also : b < current.clock) :
    request (withCutoff scope a) current signer .review = request (withCutoff scope b) current signer .review := by
  simp only [request, advance, if_pos early, if_pos also]

private theorem next_review_state_same {a b : ℚ} (early : a < current.clock) (also : b < current.clock) :
    (law base (withCutoff scope a)).step current (request (withCutoff scope a) current first .review) =
      (law base (withCutoff scope b)).step current (request (withCutoff scope b) current first .review) := by
  rw [review_request_same scope current first early also]
  exact step_same_cell base scope _ _ (iff_of_false (not_le.mpr early) (not_le.mpr also))

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem review_step_keeps_clock (active : RawLaw Party Good Port (State Party Technology) Instrument)
    (before : Raw) (action : Req) :
    (active.step before action).clock = before.clock := by
  unfold RawLaw.step
  split <;> rfl

/-- Two independent actual debit positions at the appointment, on the
same inventory and holder. Signature authority remains tied to those
original reviewers and their own material cells. -/
structure ReleaseReady (expiry : ℚ) : Prop where
  live : current.technology.holder ≠ none
  distinct : first ≠ second
  firstIndependent : current.technology.holder ≠ some first
  secondIndependent : current.technology.holder ≠ some second
  cost : 0 < amount Good scope.revisionCost unit
  firstPaid : (law base (withCutoff scope expiry)).Valid current
    (request (withCutoff scope expiry) current first .review)
  secondPaid :
    let active := law base (withCutoff scope expiry)
    let middle := active.step current (request (withCutoff scope expiry) current first .review)
    active.Valid middle (request (withCutoff scope expiry) middle second .review)

instance (expiry : ℚ) : Decidable (ReleaseReady base scope current first second unit expiry) := by
  let active := law base (withCutoff scope expiry)
  let middle := active.step current (request (withCutoff scope expiry) current first .review)
  let available := current.technology.holder ≠ none ∧ first ≠ second ∧
    current.technology.holder ≠ some first ∧ current.technology.holder ≠ some second ∧
    0 < amount Good scope.revisionCost unit ∧
    active.Valid current (request (withCutoff scope expiry) current first .review) ∧
    active.Valid middle (request (withCutoff scope expiry) middle second .review)
  have dec : Decidable available := inferInstance
  exact decidable_of_iff available
    ⟨fun ⟨live, distinct, independent₁, independent₂, cost, paid₁, paid₂⟩ =>
      ⟨live, distinct, independent₁, independent₂, cost, paid₁, paid₂⟩,
      fun p => ⟨p.live, p.distinct, p.firstIndependent, p.secondIndependent, p.cost, p.firstPaid, p.secondPaid⟩⟩

theorem release_ready_iff_expired_cell {a b : ℚ} (early : a < current.clock) (also : b < current.clock) :
    ReleaseReady base scope current first second unit a ↔ ReleaseReady base scope current first second unit b := by
  have forward (a b : ℚ) (early : a < current.clock) (also : b < current.clock)
      (ready : ReleaseReady base scope current first second unit a) :
      ReleaseReady base scope current first second unit b := by
    refine ⟨ready.live, ready.distinct, ready.firstIndependent, ready.secondIndependent, ready.cost, ?_, ?_⟩
    · rw [← review_request_same scope current first early also]
      exact (valid_iff_same_cell base scope _ _ (iff_of_false (not_le.mpr early) (not_le.mpr also))).mp ready.firstPaid
    · let middle := (law base (withCutoff scope a)).step current (request (withCutoff scope a) current first .review)
      have clock : middle.clock = current.clock := review_step_keeps_clock _ _ _
      have earlyMiddle : a < middle.clock := clock.symm ▸ early
      have alsoMiddle : b < middle.clock := clock.symm ▸ also
      change (law base (withCutoff scope b)).Valid
        ((law base (withCutoff scope b)).step current (request (withCutoff scope b) current first .review)) _
      rw [← next_review_state_same base scope current first early also]
      change (law base (withCutoff scope b)).Valid middle (request (withCutoff scope b) middle second .review)
      rw [← review_request_same scope middle second earlyMiddle alsoMiddle]
      exact (valid_iff_same_cell base scope _ _ (iff_of_false (not_le.mpr earlyMiddle) (not_le.mpr alsoMiddle))).mp
        ready.secondPaid
  exact ⟨forward a b early also, forward b a also early⟩

theorem reviewed_successor_same_expired_cell {a b : ℚ}
    (early : a < current.clock) (also : b < current.clock) :
    (law base (withCutoff scope a)).next current
        (reviewPair base (withCutoff scope a) current first second) =
      (law base (withCutoff scope b)).next current
        (reviewPair base (withCutoff scope b) current first second) := by
  let middle := (law base (withCutoff scope a)).step current
    (request (withCutoff scope a) current first .review)
  have clock : middle.clock = current.clock := review_step_keeps_clock _ _ _
  have firstSame := review_request_same scope current first early also
  have middleSame := next_review_state_same base scope current first early also
  have secondSame := review_request_same scope middle second (clock.symm ▸ early) (clock.symm ▸ also)
  have requests :
      reviewPair base (withCutoff scope a) current first second =
        reviewPair base (withCutoff scope b) current first second := by
    dsimp only [reviewPair]
    rw [← middleSame]
    change [request (withCutoff scope a) current first .review,
      request (withCutoff scope a) middle second .review] =
      [request (withCutoff scope b) current first .review, request (withCutoff scope b) middle second .review]
    rw [firstSame, secondSame]
  rw [requests]
  exact next_same_cell base scope _ _ (iff_of_false (not_le.mpr early) (not_le.mpr also))

theorem raw_release_consumes_generated_cutoff (expiry : ℚ) (early : expiry < current.clock)
    (ready : ReleaseReady base scope current first second unit expiry) :
    RawReview base (withCutoff scope expiry) current first second ([] : Word) :=
  raw_review base (withCutoff scope expiry) current first second early (fun _ h => False.elim (List.not_mem_nil h))
    ready.firstPaid ready.secondPaid

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
