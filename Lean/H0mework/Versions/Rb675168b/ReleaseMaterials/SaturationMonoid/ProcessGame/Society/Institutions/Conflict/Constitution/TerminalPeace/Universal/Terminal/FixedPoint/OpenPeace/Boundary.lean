import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.PaidWrite
import H0mework.Foundation.Responsibility.Observer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor originalRequirements actualUse)
open Capitalism.Universal.Abolition.Material.Migration (sourceAlphabet)
open ResponsibilityLifecycle
open NoFreeProbe (PaidReview)

abbrev Claim (Party Good Port Technology Instrument : Type) :=
  List Party × RawEvent Party Good Port Technology Instrument

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "Input" => ProgrammeSource.Input Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Offer" => ProductionOffer Party Good Port Technology Instrument
local notation "C" => Claim Party Good Port Technology Instrument

omit [DecidableEq Port] [DecidableEq Community] in
private def continuationAt (reference raw : RawCurrent Party Good Technology Instrument)
    (programme : Input) (claim : C) : Prop :=
  Supply.Registered programme raw claim.2 ∧ Supply.Period programme reference raw claim.1 claim.2

variable (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

def nativeContinuation (programme : Input) (claim : C) : Prop :=
  continuationAt origin current.physical.raw programme claim

/-- A lost continuation is a registered, fully paid option of this
original cut that the candidate programme would remove. -/
def losses (candidate : Input) : Set C :=
  {claim | nativeContinuation current current.programme claim ∧ ¬ nativeContinuation current candidate claim}

theorem mem_losses_iff (candidate : Input) (claim : C) :
    claim ∈ losses current candidate ↔ nativeContinuation current current.programme claim ∧
      ¬ nativeContinuation current candidate claim :=
  Iff.rfl

theorem losses_subset_original (candidate : Input) :
    losses current candidate ⊆ {claim | nativeContinuation current current.programme claim} :=
  fun _ lost => lost.1

theorem losses_empty_iff (candidate : Input) :
    losses current candidate = ∅ ↔
      ∀ claim, nativeContinuation current current.programme claim → nativeContinuation current candidate claim := by
  constructor
  · intro quiet claim original
    by_contra missing
    have lost : claim ∈ losses current candidate := ⟨original, missing⟩
    rw [quiet] at lost
    exact lost
  · intro preserves
    ext claim
    constructor
    · intro lost
      exact lost.2 (preserves claim lost.1)
    · intro absent
      exact False.elim absent

theorem original_programme_has_no_losses : losses current current.programme = ∅ :=
  (losses_empty_iff current current.programme).mpr fun _ original => original

/-- Adding registered options under the same material law keeps every
original paid continuation, including ones outside the selected recipe. -/
theorem no_rewrite_of_existing_alphabet_has_no_losses (candidate : Input)
    (sameLaw : candidate.law = current.programme.law)
    (extendsAlphabet : ∀ request, request ∈ sourceAlphabet current.programme current.physical.raw →
      request ∈ sourceAlphabet candidate current.physical.raw) :
    losses current candidate = ∅ := by
  apply (losses_empty_iff current candidate).mpr
  intro claim original
  refine ⟨fun request listed => extendsAlphabet request (original.1 request listed), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [sameLaw] using original.2.own
  · simpa only [OriginalNeedFloor, originalRequirements, actualUse, sameLaw] using original.2.originalFloor
  · simpa only [OriginalNeedFloor, originalRequirements, actualUse, sameLaw] using original.2.currentFloor
  · simpa only [sameLaw] using original.2.positiveClock

theorem adding_attempts_without_rewriting_technique_has_no_losses (offer : Offer)
    (sameTechnique : offer.technique = current.programme.law.technique) :
    losses current (reviseProgramme current.programme offer) = ∅ := by
  apply no_rewrite_of_existing_alphabet_has_no_losses
  · change { current.programme.law with technique := offer.technique } = current.programme.law
    rw [sameTechnique]
  · intro request listed
    change request ∈ (current.programme.localAttempts current.physical.raw ++ (offer.pilot ++ offer.attempts)) ++
      ProgrammeSource.wordAt current.programme current.physical.raw
    rcases List.mem_append.mp listed with localAttempt | registered
    · exact List.mem_append_left _ (List.mem_append_left _ localAttempt)
    · exact List.mem_append_right _ registered

theorem original_roster_has_its_paid_continuation :
    nativeContinuation current current.programme (people, current.move.word) :=
  ⟨current.move.registered, current.move.paid⟩

theorem original_person_has_an_independent_continuation (person : Party) (listed : person ∈ people) :
    ∃ word, nativeContinuation current current.programme ([person], word) :=
  current.move.personal person listed

variable {current} {bid : ReviewBid Party Good Port Technology Instrument}

/-- Compare at the before-state read by the actual paid material visit.
The candidate has no place in the original production write. -/
def paidLosses (paid : PaidReview current bid) (candidate : Input) : Set C :=
  let read := paid.round.visit.read
  {claim | continuationAt origin read.before.raw read.programme claim ∧
    ¬ continuationAt origin read.before.raw candidate claim}

theorem paidLosses_eq (paid : PaidReview current bid) (candidate : Input) :
    paidLosses paid candidate = losses current candidate := by
  unfold paidLosses losses nativeContinuation
  dsimp only
  rw [paid.round.before, paid.round.programmeNext, paid.programme]

theorem paid_read_has_no_losses_under_its_own_programme (paid : PaidReview current bid) :
    paidLosses paid paid.round.visit.read.programme = ∅ := by
  rw [paidLosses_eq, paid.round.programmeNext, paid.programme]
  exact original_programme_has_no_losses current

/-- The two candidates are compared on the actual paid before-state,
including the original registered words and their material requirements. -/
def hiddenPaidContinuationLoss {Request Observation : Type*} (paid : PaidReview current bid)
    (observe : Request → Observation) (candidate : Request → Input) (left right : Request)
    (same : observe left = observe right) (claim : C)
    (retained : nativeContinuation current (candidate left) claim)
    (removed : claim ∈ paidLosses paid (candidate right)) :
    HiddenNullWitness observe (fun request => paidLosses paid (candidate request)) where
  left := left
  right := right
  sameObservation := same
  differentDisposition := by
    intro sameLosses
    rw [← sameLosses, paidLosses_eq] at removed
    exact removed.2 retained

def hiddenSamePaidWord (paid : PaidReview current bid) (left right : Input) (claim : C)
    (retained : nativeContinuation current left claim) (removed : claim ∈ paidLosses paid right) :
    HiddenNullWitness (fun _ : Input => bid.attempted) (paidLosses paid) :=
  hiddenPaidContinuationLoss paid (fun _ => bid.attempted) id left right rfl claim retained removed

section Observer

variable (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

/-- An original executable continuation distinguishes the two candidates
even when their old presentations are identical. -/
def hiddenContinuationLoss {Request Observation : Type*}
    (observe : Request → Observation) (candidate : Request → Input) (left right : Request)
    (same : observe left = observe right) (claim : C)
    (retained : nativeContinuation current (candidate left) claim)
    (removed : claim ∈ losses current (candidate right)) :
    HiddenNullWitness observe (fun request => losses current (candidate request)) where
  left := left
  right := right
  sameObservation := same
  differentDisposition := by
    intro sameLosses
    have impossible : claim ∈ losses current (candidate left) := sameLosses ▸ removed
    exact impossible.2 retained

theorem no_exact_loss_classifier {Request Observation : Type*}
    (observe : Request → Observation) (candidate : Request → Input)
    (hidden : HiddenNullWitness observe (fun request => losses current (candidate request))) :
    ¬ ∃ classify : Observation → Set C, ∀ request, classify (observe request) = losses current (candidate request) := by
  rintro ⟨classify, reads⟩
  exact hidden.not_consumerSafe (ConsumerSafe.of_factorization classify reads)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community] in
def oldOfferWord (offer : Offer) : Word :=
  offer.pilot ++ offer.attempts

def hiddenOldOfferLoss (left right : Offer) (same : oldOfferWord left = oldOfferWord right)
    (claim : C) (retained : nativeContinuation current (reviseProgramme current.programme left) claim)
    (removed : claim ∈ losses current (reviseProgramme current.programme right)) :
    HiddenNullWitness oldOfferWord (fun offer => losses current (reviseProgramme current.programme offer)) :=
  hiddenContinuationLoss current oldOfferWord (reviseProgramme current.programme) left right same claim retained removed

theorem old_offer_word_cannot_classify_loss (left right : Offer) (same : oldOfferWord left = oldOfferWord right)
    (claim : C) (retained : nativeContinuation current (reviseProgramme current.programme left) claim)
    (removed : claim ∈ losses current (reviseProgramme current.programme right)) :
    ¬ ∃ classify : Word → Set C, ∀ offer, classify (oldOfferWord offer) =
      losses current (reviseProgramme current.programme offer) :=
  no_exact_loss_classifier current oldOfferWord (reviseProgramme current.programme)
    (hiddenOldOfferLoss current left right same claim retained removed)

end Observer

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
