import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Round
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Revision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

/-- A candidate can demand a foreign debit even when the actual law will
refuse it. The declared incidence is read on the candidate's own word. -/
def DemandsAggression (law : RawLaw Party Good Port Technology Instrument)
    (raw : RawCurrent Party Good Technology Instrument)
    (bid : ReviewBid Party Good Port Technology Instrument) : Prop :=
  ∃ item ∈ law.rawItems raw bid.attempted, item.request.signer = bid.payer ∧
    ∃ victim good, community victim ≠ community bid.payer ∧ victim ∉ item.request.consents ∧
      flowAt (law.credit item.before item.request) victim good <
        flowAt (law.debit item.before item.request) victim good

structure Replies (Party Good Port Technology Instrument : Type) where
  review : AnyAuthoritativeRootCurrent.{0} → RawCurrent Party Good Technology Instrument →
    ReviewBid Party Good Port Technology Instrument → Party → Bool
  revision : RevisionAnswers Party Good Port Technology Instrument

variable (replies : Replies Party Good Port Technology Instrument)
  (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

variable (bid : ReviewBid Party Good Port Technology Instrument)

/-- The source pays review only from the actual signer's current output.
At least one material cell still grows after all review expenses. -/
structure AccountableReview : Prop where
  standing : bid.payer ∈ people
  demand : DemandsAggression (community := community) current.programme.law current.physical.raw bid
  signed : replies.review current.ledger.resident.erase current.physical.raw bid bid.payer = true
  legal : ReviewLegal current bid
  realCost : ∃ good, 0 < amount Good bid.expenses good
  fits : ReviewFits current.recipe bid.fee
  surplus : ∃ person good, bid.fee person good < current.recipe.gain person good

/-- Every submission lands on the original ledger. A hostile proposal's
material is excluded in both cases. A signed paid review consumes only
its separate actual expense; a presentation supplies no operating act. -/
def dispatch (submitted : Proposal Party Good Port Technology Instrument) : Round current := by
  classical
  exact match submitted with
  | .renew => productiveRound current .renew .renewed current.programme current.recipe
  | .review bid =>
    if review : AccountableReview replies current bid then
      paidReviewRound current bid review.legal review.fits review.surplus
    else productiveRound current (.review bid) .presentation current.programme current.recipe
  | .revise offer =>
    match inspectRevision current.programme origin people cut.raw quantum replies.revision
      current.ledger.resident.erase current.physical.raw offer with
    | .checked kit _ =>
      productiveRound current (.revise offer) .revised (reviseProgramme current.programme offer) kit.recipe
    | .refused _ _ _ | .unproductive _ _ =>
      productiveRound current (.revise offer) .revisionRefused current.programme current.recipe

theorem dispatch_keeps_the_original_public_terms (submitted : Proposal Party Good Port Technology Instrument) :
    KeepsPublicTerms current.programme (dispatch replies current submitted).next.programme := by
  classical
  cases submitted with
  | renew => exact .refl _
  | review bid =>
    by_cases admissible : AccountableReview replies current bid
    · simp only [dispatch, dif_pos admissible]
      exact .refl _
    · simp only [dispatch, dif_neg admissible]
      exact .refl _
  | revise offer =>
    simp only [dispatch]
    cases inspectRevision current.programme origin people cut.raw quantum replies.revision
      current.ledger.resident.erase current.physical.raw offer with
    | checked _ _ => exact reviseProgramme_keeps_public_terms _ _
    | refused _ _ _ => exact .refl _
    | unproductive _ _ => exact .refl _

theorem an_accepted_revision_is_its_actual_trial (offer : ProductionOffer Party Good Port Technology Instrument)
    (kit : RevisionKit current.programme origin people cut.raw quantum offer)
    (approved : RevisionApproval replies.revision current.ledger.resident.erase current.physical.raw people offer)
    (selected : inspectRevision current.programme origin people cut.raw quantum replies.revision
      current.ledger.resident.erase current.physical.raw offer = .checked kit approved) :
    let round := dispatch replies current (.revise offer)
    round.visit.read.disposition = .revised ∧ round.visit.read.commands = offer.pilot ∧
      round.next.programme = reviseProgramme current.programme offer ∧
      round.next.ledger.stack.balances = current.ledger.stack.balances := by
  dsimp only
  refine ⟨?_, ?_, ?_, (dispatch replies current (.revise offer)).rows⟩
  all_goals
    simp only [dispatch, selected]
  · rfl
  · exact (productiveRound_reads_selected_production current (.revise offer) .revised _ kit.recipe).2.2.2.trans
      (kit.at_opening current.physical.raw current.reserved)
  · rfl

def materialPayoff (bid : ReviewBid Party Good Port Technology Instrument)
    (actual peaceful : RawCurrent Party Good Technology Instrument) (weight : Good → ℚ) : ℚ :=
  ∑ good ∈ (bid.expenses.map Prod.fst).toFinset, weight good *
    (actual.stock bid.payer good - peaceful.stock bid.payer good)

omit [DecidableEq Party] [DecidableEq Port] [DecidableEq Instrument] in
private theorem positive_expense_is_listed (good : Good) (positive : 0 < amount Good bid.expenses good) :
    good ∈ bid.expenses.map Prod.fst := by
  by_contra absent
  have zero : amount Good bid.expenses good = 0 := by
    unfold amount
    apply List.sum_eq_zero
    intro value listed
    obtain ⟨lot, present, rfl⟩ := List.mem_map.mp listed
    have other : lot.1 ≠ good := fun same => absent (same ▸ List.mem_map_of_mem present)
    exact if_neg other
  rw [zero] at positive
  exact (lt_irrefl 0 positive)

theorem every_accountable_attack_is_strictly_costly
    (review : AccountableReview replies current bid) (weight : Good → ℚ) (valuable : ∀ good, 0 < weight good) :
    let round := dispatch replies current (.review bid)
    let peaceful := current.move.next
    round.visit.read.disposition = .reviewed ∧ round.next.programme = current.programme ∧
      (∀ good, round.next.physical.raw.stock bid.payer good - peaceful.stock bid.payer good =
        -(amount Good bid.parts.application good + amount Good bid.parts.review good +
          amount Good bid.parts.opportunity good)) ∧
      (∀ person, person ≠ bid.payer → ∀ good, round.next.physical.raw.stock person good = peaceful.stock person good) ∧
      round.next.physical.raw.claims = peaceful.claims ∧ round.next.physical.raw.technology = peaceful.technology ∧
      round.next.physical.raw.clock = peaceful.clock ∧
      materialPayoff bid round.next.physical.raw peaceful weight < 0 := by
  dsimp only
  simp only [dispatch, dif_pos review]
  have exact := paidReviewRound_reads_the_payers_whole_cost current bid review.legal review.fits review.surplus
  have stock := exact.2.2.2.2.2.2
  refine ⟨exact.1, exact.2.1, ?_, ?_, exact.2.2.1, exact.2.2.2.1, exact.2.2.2.2.1, ?_⟩
  · intro good
    simpa only [ReviewBid.fee, if_pos rfl, if_true, bid.parts.amount_bundle] using stock bid.payer good
  · intro person others good
    have same := stock person good
    rw [ReviewBid.fee, if_neg others, neg_zero] at same
    exact sub_eq_zero.mp same
  · unfold materialPayoff
    have written := charged_native_write current.physical current.move.paid review.legal
    have actual : (paidReviewRound current bid review.legal review.fits review.surplus).next.physical.raw =
        afterCharge current.programme current.physical.raw current.move.word bid.payer bid.port bid.expenses :=
      congrArg (fun next : Runtime.Native Party Good Port Technology Instrument => next.raw) written.2.2
    rw [actual]
    obtain ⟨good, positive⟩ := review.realCost
    exact a_positive_paid_lot_makes_every_positive_weighted_portfolio_strictly_worse
      current.programme current.physical current.move.word bid.payer bid.port bid.expenses review.legal
      _ weight (fun material _ => valuable material)
      ⟨good, List.mem_toFinset.mpr (positive_expense_is_listed bid good positive), positive⟩

theorem an_unfunded_presentation_leaves_no_material_windfall
    (unfunded : ¬ AccountableReview replies current bid) (weight : Good → ℚ) :
    let round := dispatch replies current (.review bid)
    round.visit.read.disposition = .presentation ∧ round.next.programme = current.programme ∧
      round.next.physical.raw = current.move.next ∧
      materialPayoff bid round.next.physical.raw current.move.next weight = 0 := by
  dsimp only
  simp only [dispatch, dif_neg unfunded]
  have exact := productiveRound_reads_selected_production current (.review bid) .presentation current.programme current.recipe
  refine ⟨exact.1, exact.2.2.1, exact.2.1, ?_⟩
  simp [exact.2.1, materialPayoff]

theorem negative_private_payoff_iff_the_attack_has_a_paid_review
    (weight : Good → ℚ) (valuable : ∀ good, 0 < weight good) :
    materialPayoff bid (dispatch replies current (.review bid)).next.physical.raw current.move.next weight < 0 ↔
      AccountableReview replies current bid := by
  constructor
  · intro negative
    by_contra free
    rw [(an_unfunded_presentation_leaves_no_material_windfall replies current bid free weight).2.2.2] at negative
    exact (lt_irrefl 0 negative)
  · intro review
    exact (every_accountable_attack_is_strictly_costly replies current bid review weight valuable).2.2.2.2.2.2.2

theorem zero_fee_submissions_have_the_same_production_effect
    (zero : ∀ good, amount Good bid.expenses good = 0) :
    let round := dispatch replies current (.review bid)
    round.visit.read.disposition = .presentation ∧
      round.visit.read.commands = current.move.word ∧ round.next.physical.raw = current.move.next := by
  have noCost : ¬ AccountableReview replies current bid := by
    intro admitted
    obtain ⟨good, positive⟩ := admitted.realCost
    rw [zero good] at positive
    exact (lt_irrefl 0 positive)
  dsimp only
  simp only [dispatch, dif_neg noCost]
  have ordinary := productiveRound_reads_selected_production current (.review bid) .presentation current.programme current.recipe
  exact ⟨ordinary.1, ordinary.2.2.2, ordinary.2.1⟩

theorem accountable_review_posts_cost_at_the_actual_position
    (review : AccountableReview replies current bid) :
    (dispatch replies current (.review bid)).visit.read.effect.execution.items[current.move.word.length]? =
      some (reviewItem current.programme current.physical.raw current.move.word bid.payer bid.port bid.expenses) := by
  have selected : dispatch replies current (.review bid) =
      paidReviewRound current bid review.legal review.fits review.surplus := dif_pos review
  rw [selected]
  exact paidReviewRound_charges_the_actual_last_item current bid review.legal review.fits review.surplus

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
