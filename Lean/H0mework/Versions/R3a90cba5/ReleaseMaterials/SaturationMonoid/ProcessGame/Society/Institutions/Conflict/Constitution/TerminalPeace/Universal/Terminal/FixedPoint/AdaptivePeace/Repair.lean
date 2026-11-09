import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Exposure
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.PaidWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe (PaidReview)
open private positive_expense_is_listed from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}
  {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
  {bid : ReviewBid Party Good Port Technology Instrument}

/-- The original paid read supplies the affected coordinates. -/
def witnessed (paid : PaidReview current bid) : Finset (Party × Good) :=
  demanded community paid.round.visit.read.programme.law paid.round.visit.read.before.raw bid

theorem mem_witnessed_iff (paid : PaidReview current bid) (key : Party × Good) :
    key ∈ witnessed paid ↔ demandsAt community current.programme.law current.physical.raw bid key := by
  rw [witnessed, mem_demanded_iff, paid.round.before, paid.round.programmeNext, paid.programme]

variable (known : Finset (Party × Good)) (paid : PaidReview current bid)

/-- The admission repair adds exactly the paid witness at the charged
successor. Production and the whole original stack continue from it. -/
def repair : Installation.Live.Landed seed community cut (Finset (Party × Good)) :=
  Installation.Live.publish paid.round.next.ledger (known ∪ witnessed paid) true

def repairedCurrent : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase) :=
  { paid.round.next with ledger := (repair known paid).state }

theorem repair_read : (repair known paid).read = known ∪ witnessed paid :=
  Installation.Live.publish_reads_the_exact_payload _ _ _

theorem mem_repair_iff (key : Party × Good) :
    key ∈ (repair known paid).read ↔ key ∈ known ∨
      demandsAt community current.programme.law current.physical.raw bid key := by
  rw [repair_read, Finset.mem_union, mem_witnessed_iff]

theorem repair_least_iff (candidate : Finset (Party × Good)) :
    (repair known paid).read ⊆ candidate ↔ known ⊆ candidate ∧ witnessed paid ⊆ candidate := by
  rw [repair_read]
  constructor
  · intro includes
    exact ⟨fun _ old => includes (Finset.mem_union.mpr (.inl old)),
      fun _ new => includes (Finset.mem_union.mpr (.inr new))⟩
  · rintro ⟨old, new⟩ key listed
    exact (Finset.mem_union.mp listed).elim (old ·) (new ·)

theorem repair_strict {key : Party × Good} (demand : key ∈ witnessed paid) (new : key ∉ known) :
    known ⊂ (repair known paid).read := by
  rw [repair_read, Finset.ssubset_iff_subset_ne]
  refine ⟨fun _ old => Finset.mem_union.mpr (.inl old), ?_⟩
  intro same
  have added : key ∈ known ∪ witnessed paid := Finset.mem_union.mpr (.inr demand)
  rw [← same] at added
  exact new added

theorem repair_canonical_next :
    (⟨paid.round.next.ledger.world,
      (Installation.Live.action paid.round.next.ledger (repair known paid).read
        true).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      (repairedCurrent known paid).ledger.resident.erase :=
  Installation.Live.the_canonical_write_is_the_published_whole_state _ _ _

theorem repair_stack :
    (repairedCurrent known paid).ledger.stack = paid.round.next.ledger.stack :=
  Installation.Live.publish_preserves_the_entire_stack _ _ _

theorem repair_rows :
    (repairedCurrent known paid).ledger.stack.balances = current.ledger.stack.balances :=
  paid.round.rows

theorem repair_retains_prior_projection
    (projection : paid.round.next.ledger.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (repair known paid).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (paid.round.next.ledger.resident.root.source.base.projectionLaw.outcomeAt projection
        (paid.round.next.ledger.resident.root.emitted paid.round.next.ledger.resident.visit.current)) :=
  Installation.Live.earlier_reads_are_kept_at_the_landing _ _ _ projection

theorem repair_physical :
    (repairedCurrent known paid).physical = paid.round.next.physical :=
  rfl

theorem repair_programme :
    (repairedCurrent known paid).programme = current.programme :=
  paid.programme

theorem repair_keeps_public_terms :
    KeepsPublicTerms current.programme (repairedCurrent known paid).programme :=
  paid.keepsPublicTerms

theorem repair_gain (person : Party) (good : Good) :
    (repairedCurrent known paid).recipe.gain person good = paid.round.next.recipe.gain person good :=
  rfl

theorem repair_preserves_native_execution (word : RawEvent Party Good Port Technology Instrument) :
    Physical.Public.compile (repairedCurrent known paid).programme
      (repairedCurrent known paid).physical (.execute word) =
    Physical.Public.compile paid.round.next.programme paid.round.next.physical (.execute word) :=
  rfl

theorem repair_has_independent_exit (person : Party) (listed : person ∈ people) :
    ∃ word, Supply.Registered (repairedCurrent known paid).programme (repairedCurrent known paid).physical.raw word ∧
      Supply.Period (repairedCurrent known paid).programme origin (repairedCurrent known paid).physical.raw [person] word :=
  (repairedCurrent known paid).move.personal person listed

theorem repair_keeps_live_round :
    let read := paid.round.visit.read
    let after := repairedCurrent known paid
    read.effect.isAccepted = true ∧ read.effect.next = after.physical ∧
      OriginalNeedFloor read.programme origin current.physical.raw people read.commands ∧
      OriginalNeedFloor read.programme current.physical.raw current.physical.raw people read.commands ∧
      (∀ item ∈ read.effect.execution.items, ∀ key, Reparation.loss read.programme.law community item key = 0) ∧
      current.physical.raw.clock + quantum ≤ after.physical.raw.clock ∧
      after.physical.raw.clock = current.move.next.clock ∧
      (∃ person good, current.physical.raw.stock person good < after.physical.raw.stock person good) :=
  ⟨paid.round.realWrite, paid.round.physicalNext, paid.round.needs.1, paid.round.needs.2,
    paid.round.noDamage, paid.round.clock, paid.settledClock, paid.round.growth⟩

theorem repair_original_expense :
    (repairedCurrent known paid).physical = paid.round.visit.read.effect.next ∧
    ∃ item, paid.round.visit.read.effect.execution.items[current.move.word.length]? = some item ∧
      item.request.signer = bid.payer ∧
      paid.round.visit.read.programme.law.actualDebit item.before item.request = locate bid.payer bid.expenses ∧
      paid.round.visit.read.programme.law.actualCredit item.before item.request = [] :=
  ⟨paid.round.physicalNext.symm, paid.original_expense⟩

include paid in
private theorem paid_expenses_nonnegative (good : Good) : 0 ≤ amount Good bid.expenses good := by
  have debit := paid.debit
  rw [paid.round.programmeNext, paid.programme] at debit
  unfold RawLaw.actualDebit at debit
  split at debit
  · rename_i legal
    exact charged_amount_nonnegative legal good
  · have empty : bid.expenses = [] := by simpa [locate] using debit.symm
    simp [empty, amount]

theorem repair_weighted_debit (observed : Finset Good) (weight : Good → ℚ) :
    (∑ good ∈ observed, weight good * ((repairedCurrent known paid).physical.raw.stock bid.payer good -
      current.move.next.stock bid.payer good)) = -(∑ good ∈ observed, weight good * amount Good bid.expenses good) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro good _
  change weight good * (paid.round.next.physical.raw.stock bid.payer good -
    current.move.next.stock bid.payer good) = _
  rw [paid.stock, ReviewBid.fee, if_pos rfl, mul_neg]

theorem repair_weighted_loss (observed : Finset Good) (weight : Good → ℚ)
    (valuable : ∀ good ∈ observed, 0 < weight good)
    (actual : ∃ good ∈ observed, 0 < amount Good bid.expenses good) :
    (∑ good ∈ observed, weight good * ((repairedCurrent known paid).physical.raw.stock bid.payer good -
      current.move.next.stock bid.payer good)) < 0 := by
  rw [repair_weighted_debit]
  apply neg_lt_zero.mpr
  apply Finset.sum_pos'
  · intro good listed
    exact mul_nonneg (valuable good listed).le (paid_expenses_nonnegative paid good)
  · obtain ⟨good, listed, positive⟩ := actual
    exact ⟨good, listed, mul_pos (valuable good listed) positive⟩

theorem repair_material_payoff_negative (weight : Good → ℚ) (valuable : ∀ good, 0 < weight good) :
    materialPayoff bid (repairedCurrent known paid).physical.raw current.move.next weight < 0 := by
  obtain ⟨good, positive⟩ := paid.positive
  exact repair_weighted_loss known paid _ weight (fun good _ => valuable good)
    ⟨good, List.mem_toFinset.mpr (positive_expense_is_listed bid good positive), positive⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace
