import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable {tariff : Tariff Party Good Port Technology Instrument} {home : AnyAuthoritativeRootCurrent.{0}}
  {orders : PaymentOrders Party Good Port Technology Instrument} {replies : Replies Party Good Port Technology Instrument}
  {before : State (seed := seed) (cut := cut) (community := community) origin people quantum}

local notation "Keys" => Finset (Party × Good)
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Terms" => (Prepayment.registeredTerms (seed := seed) (cut := cut)
  (community := community) (origin := origin) (people := people) (quantum := quantum))
local notation "OrderFor" wire => Prepayment.CanPrepay Terms tariff home orders
  (Terms before.native) before.native.physical.raw.clock wire

variable (step : Step tariff home orders replies before)

theorem Step.no_actual_damage :
    ∀ item ∈ step.source.round.visit.read.effect.execution.items, ∀ key,
      Reparation.loss step.source.round.visit.read.programme.law community item key = 0 :=
  step.source.round.noDamage

/-- The amendment preserves the whole native execution surface, hence
every previously available productive word and personal exit word. -/
theorem Step.keeps_every_native_word (word : Word) :
    HEq (Physical.Public.compile step.next.native.programme step.next.native.physical (.execute word))
      (Physical.Public.compile step.source.next.programme step.source.next.physical (.execute word)) := by
  cases step <;> rfl

theorem Step.keeps_every_safe_continuation (roster : List Party) (word : Word) :
    (Supply.Registered step.next.native.programme step.next.native.physical.raw word ∧
      Supply.Period step.next.native.programme origin step.next.native.physical.raw roster word) ↔
    (Supply.Registered step.source.next.programme step.source.next.physical.raw word ∧
      Supply.Period step.source.next.programme origin step.source.next.physical.raw roster word) := by
  rw [step.same_programme, step.same_physical_successor]

theorem Step.keeps_productive_capacity (person : Party) (good : Good) :
    step.next.native.recipe.gain person good = step.source.next.recipe.gain person good := by
  cases step <;> rfl

theorem Step.keeps_public_terms :
    KeepsPublicTerms before.native.programme step.next.native.programme := by
  rw [step.same_programme]
  exact step.source.keepsPublicTerms

theorem Step.paid_attack_is_strictly_costly
    {wire : Wire Party Good Port Technology Instrument} {order : OrderFor wire}
    {paid : PaidReview before.native (bill tariff wire)}
    (paidVisit : step.source = .prepaid wire order paid) (weight : Good → ℚ)
    (valuable : ∀ good, 0 < weight good) :
    materialPayoff (bill tariff wire) step.next.native.physical.raw before.native.move.next weight < 0 := by
  have same : step.next.native.physical = (repairedCurrent before.covered paid).physical := by
    rw [step.same_physical_successor, paidVisit]
    rfl
  rw [same]
  exact repair_material_payoff_negative before.covered paid weight valuable

/-- The remaining scopes which can open a fresh failure inquiry. The
same class may still present or pay for a fixed refusal. -/
def unsealed (state : State (seed := seed) (cut := cut) (community := community) origin people quantum) :
    Set (Party × Good) :=
  {key | key ∉ state.covered}

theorem Step.unsealed_can_only_shrink : unsealed step.next ⊆ unsealed before :=
  fun _ openLater closedEarlier => openLater (step.keeps_coverage closedEarlier)

theorem Step.strictly_shrinks_unsealed
    (novel : ¬ paidExposure tariff home orders replies before step.source ⊆ before.covered) :
    unsealed step.next ⊂ unsealed before := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨step.unsealed_can_only_shrink, ?_⟩
  intro same
  apply novel
  intro key observed
  by_contra fresh
  have earlier : key ∈ unsealed before := fresh
  rw [← same] at earlier
  exact earlier (step.seals_every_witness observed)

/-- The actual branch determines its material receipt and the single
least addition that was written. -/
structure AmendmentAt where
  private mk ::
  wire : Wire Party Good Port Technology Instrument
  order : OrderFor wire
  paid : PaidReview before.native (bill tariff wire)
  novel : ¬ witnessed paid ⊆ before.covered
  occurred : step = .amended wire order paid novel

namespace AmendmentAt

variable {step} (amendment : AmendmentAt step)

def write : Installation.Live.Landed seed community cut Keys :=
  repair before.covered amendment.paid

theorem actual_first_write :
    step.amendment = some amendment.write ∧ step.next.amendment = some amendment.write ∧
      step.reply = .amended ∧
      (⟨amendment.paid.round.next.ledger.world,
        (Installation.Live.action amendment.paid.round.next.ledger amendment.write.read
          true).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
        step.next.native.ledger.resident.erase := by
  obtain ⟨wire, order, paid, novel, rfl⟩ := amendment
  exact ⟨rfl, rfl, rfl, repair_canonical_next before.covered paid⟩

theorem least_amendment (candidate : Keys) :
    amendment.write.read ⊆ candidate ↔ before.covered ⊆ candidate ∧ witnessed amendment.paid ⊆ candidate :=
  repair_least_iff before.covered amendment.paid candidate

theorem every_new_scope_has_its_original_exposure (key : Party × Good) :
    key ∈ (amendment.write.read \ before.covered) ↔ key ∉ before.covered ∧
      demandsAt community before.native.programme.law before.native.physical.raw (bill tariff amendment.wire) key := by
  rw [Finset.mem_sdiff, AmendmentAt.write, mem_repair_iff]
  tauto

theorem strictly_negative (weight : Good → ℚ) (valuable : ∀ good, 0 < weight good) :
    materialPayoff (bill tariff amendment.wire) step.next.native.physical.raw before.native.move.next weight < 0 := by
  obtain ⟨wire, order, paid, novel, rfl⟩ := amendment
  exact repair_material_payoff_negative before.covered paid weight valuable

end AmendmentAt

/-- Every newly exposed scope comes from an already paid occurrence.
The first write is the original root's least cumulative repair. -/
theorem every_novel_attack_generates_stronger_peace
    (novel : ¬ paidExposure tariff home orders replies before step.source ⊆ before.covered) :
    ∃ amendment : AmendmentAt step,
      step.amendment = some amendment.write ∧ step.next.amendment = some amendment.write ∧
      (⟨amendment.paid.round.next.ledger.world,
        (Installation.Live.action amendment.paid.round.next.ledger amendment.write.read
          true).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
          step.next.native.ledger.resident.erase ∧
      (∀ candidate : Keys,
        amendment.write.read ⊆ candidate ↔ before.covered ⊆ candidate ∧ witnessed amendment.paid ⊆ candidate) ∧
      unsealed step.next ⊂ unsealed before ∧
      (∀ weight : Good → ℚ, (∀ good, 0 < weight good) →
        materialPayoff (bill tariff amendment.wire) step.next.native.physical.raw before.native.move.next weight < 0) ∧
      (∀ item ∈ step.source.round.visit.read.effect.execution.items, ∀ key,
        Reparation.loss step.source.round.visit.read.programme.law community item key = 0) ∧
      (∀ word : Word, HEq
        (Physical.Public.compile step.next.native.programme step.next.native.physical (.execute word))
        (Physical.Public.compile step.source.next.programme step.source.next.physical (.execute word))) ∧
      (∀ person good, step.next.native.recipe.gain person good = step.source.next.recipe.gain person good) ∧
      HEq step.next.native.ledger.stack step.source.next.ledger.stack ∧
      KeepsPublicTerms before.native.programme step.next.native.programme := by
  have generated : Nonempty (AmendmentAt step) := by
    cases step with
    | ordinary _ safe =>
      exact (novel (by simpa only [Step.source, safe] using Finset.empty_subset before.covered)).elim
    | refused _ _ _ _ covered => exact (novel covered).elim
    | amended wire order paid fresh => exact ⟨⟨wire, order, paid, fresh, rfl⟩⟩
  obtain ⟨amendment⟩ := generated
  obtain ⟨written, installed, _, successor⟩ := amendment.actual_first_write
  exact ⟨amendment, written, installed, successor, amendment.least_amendment, step.strictly_shrinks_unsealed novel,
    amendment.strictly_negative, step.no_actual_damage, step.keeps_every_native_word, step.keeps_productive_capacity,
    step.same_stack, step.keeps_public_terms⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace
