import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Scope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open NoFreeProbe (PaidReview)

structure NovelPoint {α : Type} (observed earlier : Set α) where
  point : α
  observedHere : point ∈ observed
  absentEarlier : point ∉ earlier

theorem NovelPoint.excludesCoverage {α : Type} {observed earlier : Set α} (found : NovelPoint observed earlier) :
    ¬ observed ⊆ earlier :=
  fun known => found.absentEarlier (known found.observedHere)

def firstNovel {α : Type} {observed earlier : Set α}
    (readObserved : ReadSet observed) (readEarlier : ReadSet earlier) (points : List α) :
    Option (NovelPoint observed earlier) :=
  points.findSome? fun point =>
    match readObserved point, readEarlier point with
    | some (.isTrue present), some (.isFalse absent) => some ⟨point, present, absent⟩
    | _, _ => none


theorem firstNovel_finds_a_tested_witness {α : Type} {observed earlier : Set α}
    (readObserved : ReadSet observed) (readEarlier : ReadSet earlier) (points : List α)
    (witness : NovelPoint observed earlier) (tested : witness.point ∈ points)
    (newRead : readObserved witness.point = some (.isTrue witness.observedHere))
    (oldRead : readEarlier witness.point = some (.isFalse witness.absentEarlier)) :
    ∃ selected, firstNovel readObserved readEarlier points = some selected := by
  cases scan : firstNovel readObserved readEarlier points with
  | some selected => exact ⟨selected, rfl⟩
  | none =>
    unfold firstNovel at scan
    have missed := (List.findSome?_eq_none_iff.mp scan) witness.point tested
    simp [newRead, oldRead] at missed

variable {Party Good Port Technology Instrument : Type}

local notation "Prog" => ProgrammeSource.Input Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- Checked source edits identify changed parts of a proposal using its
literal construction. Arbitrary proposed programmes may still be probed. -/
inductive ProposalCode (old : ProgrammeSource.Input Party Good Port Technology Instrument) :
    ProgrammeSource.Input Party Good Port Technology Instrument → Type 1
  | raw (proposal : Prog) : ProposalCode old proposal
  | observed (proposal : Prog) {Value : Type} (exact : DecidableEq Value) (read : Prog → Value) :
      ProposalCode old proposal
  | sameLaw (proposal : Prog) (law : proposal.law = old.law) : ProposalCode old proposal
  | attempts (emit : Raw → Word) : ProposalCode old { old with localAttempts := emit }
  | offer (offer : ProductionOffer Party Good Port Technology Instrument) :
      ProposalCode old (reviseProgramme old offer)

namespace ProposalCode

variable {old proposal : ProgrammeSource.Input Party Good Port Technology Instrument}

def material (code : ProposalCode old proposal) : Option (PLift (proposal.law = old.law)) :=
  match code with
  | .raw _ | .observed _ _ _ => none
  | .sameLaw _ law => some ⟨law⟩
  | .attempts _ => some ⟨rfl⟩
  | .offer _ => none

variable [DecidableEq (Request Party Good Port Technology Instrument)]

def terms (code : ProposalCode old proposal) : Checked (¬ KeepsPublicTerms old proposal) :=
  match code with
  | .attempts _ => some (.isFalse (fun different => different rfl))
  | .offer added => some (.isFalse (fun different => different (reviseProgramme_keeps_public_terms old added)))
  | .observed _ compare read =>
    letI := compare
    (checkTermField old proposal read).orElse fun _ => checkTerms old proposal
  | .raw _ | .sameLaw _ _ => checkTerms old proposal

end ProposalCode

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]
  {Community : Type} [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}
  {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
  {bid : ReviewBid Party Good Port Technology Instrument}

private theorem noMaterialLoss (paid : PaidReview current bid) (proposal : Prog)
    (law : proposal.law = current.programme.law)
    (kept : ∀ request ∈ Capitalism.Universal.Abolition.Material.Migration.sourceAlphabet
      current.programme current.physical.raw,
      request ∈ Capitalism.Universal.Abolition.Material.Migration.sourceAlphabet proposal current.physical.raw) :
    paidLosses paid proposal = ∅ := by
  rw [paidLosses_eq]
  exact no_rewrite_of_existing_alphabet_has_no_losses current proposal law kept

private theorem coveredWithNoLoss (paid : PaidReview current bid) (proposal : Prog)
    (earlier : Set (Effect Party Good Port Technology Instrument))
    (material : paidLosses paid proposal = ∅)
    (protectedTerms : ¬ KeepsPublicTerms current.programme proposal → Sum.inr () ∈ earlier) :
    paidEffects paid proposal ⊆ earlier := by
  intro point present
  cases point with
  | inl claim =>
    rw [paidEffects_loss, material] at present
    exact present.elim
  | inr value =>
    cases value
    exact protectedTerms ((paidEffects_public_terms paid proposal).mp present)

variable [DecidableEq (Request Party Good Port Technology Instrument)]

/-- A finite registered alphabet check yields a proof for all lengths
under the same material law. The public-term direction is checked
independently against the actual older language. -/
def paidCoverage (paid : PaidReview current bid) {proposal : Prog}
    (code : ProposalCode current.programme proposal)
    {earlier : Set (Effect Party Good Port Technology Instrument)}
    (readEarlier : ReadSet earlier) :
    Option (PLift (paidEffects paid proposal ⊆ earlier)) :=
  match code.material, checkAlphabet current.programme proposal current.physical.raw with
  | some same, .isTrue kept =>
    let material := noMaterialLoss paid proposal same.down kept
    match code.terms, readEarlier (.inr ()) with
    | some (.isFalse unchanged), _ =>
      some ⟨coveredWithNoLoss paid proposal earlier material (fun different => (unchanged different).elim)⟩
    | _, some (.isTrue known) =>
      some ⟨coveredWithNoLoss paid proposal earlier material (fun _ => known)⟩
    | _, _ => none
  | _, _ => none

/-- Probe the physical words actually run this period and their personal
restrictions. An additional finite submitted word can be examined at
any length. Exhausting these probes does not assert global coverage. -/
def sourceProbes (roster : List Party) (word : Word) :
    List (Effect Party Good Port Technology Instrument) :=
  .inr () :: .inl (roster, word) ::
    roster.map (fun person => .inl ([person], word.filter (fun request => request.signer == person)))

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
