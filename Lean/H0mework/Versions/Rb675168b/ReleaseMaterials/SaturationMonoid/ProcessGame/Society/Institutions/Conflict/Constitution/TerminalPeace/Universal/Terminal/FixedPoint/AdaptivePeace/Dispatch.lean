import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Repair
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Registered

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "Native" => Current (seed := seed) (cut := cut) (community := community) origin people quantum
local notation "Keys" => Finset (Party × Good)
local notation "Patch" => Installation.Live.Landed seed community cut Keys
local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "Slot" => NoFreeProbe.Due Party Good Port Technology Instrument

/-- The defence in force is read from the last actual amendment of
this run. A productive visit carries that original read forward. -/
structure State (origin : RawCurrent Party Good Technology Instrument) (people : List Party) (quantum : ℚ) where
  private mk ::
  native : Current (seed := seed) (cut := cut) (community := community) origin people quantum
  amendment : Option Patch

local notation "St" => State (seed := seed) (cut := cut) (community := community) origin people quantum

private def State.start (current : Native) : St :=
  ⟨current, none⟩

def State.covered (state : St) : Keys :=
  (state.amendment.map Installation.Live.Landed.read).getD ∅

inductive Reply
  | ordinary (answer : Prepayment.Reply)
  | refused
  | amended
  deriving DecidableEq

structure Observation where
  opensAt : ℚ
  landsAt : ℚ
  reply : Reply
  deriving DecidableEq

variable (tariff : Tariff Party Good Port Technology Instrument)
  (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (before : State (seed := seed) (cut := cut) (community := community) origin people quantum)

local notation "sourceTerms" => (Prepayment.registeredTerms (seed := seed) (cut := cut)
  (community := community) (origin := origin) (people := people) (quantum := quantum))
local notation "BaseStep" => Prepayment.Step tariff replies before.native sourceTerms home orders
local notation "OrderFor" wire => Prepayment.CanPrepay sourceTerms tariff home orders
  (sourceTerms before.native) before.native.physical.raw.clock wire

def paidExposure (base : BaseStep) : Keys :=
  match base with
  | .ordinary _ _ => ∅
  | .prepaid _ _ paid => witnessed paid

inductive Step where
  | ordinary (base : BaseStep) (noBreach : paidExposure tariff home orders replies before base = ∅)
  | refused (wire : Packet) (order : OrderFor wire) (paid : PaidReview before.native (bill tariff wire))
      (breach : witnessed paid ≠ ∅) (covered : witnessed paid ⊆ before.covered)
  | amended (wire : Packet) (order : OrderFor wire) (paid : PaidReview before.native (bill tariff wire))
      (novel : ¬ witnessed paid ⊆ before.covered)

namespace Step

variable {tariff home orders replies before} (step : Step tariff home orders replies before)

def source : BaseStep :=
  match step with
  | .ordinary base _ => base
  | .refused wire order paid _ _ | .amended wire order paid _ => .prepaid wire order paid

def amendment : Option Patch :=
  match step with
  | .amended _ _ paid _ => some (repair before.covered paid)
  | _ => none

def reply : Reply :=
  match step with
  | .ordinary base _ => .ordinary base.reply
  | .refused _ _ _ _ _ => .refused
  | .amended _ _ _ _ => .amended

private def refusal {bid : ReviewBid Party Good Port Technology Instrument}
    (paid : PaidReview before.native bid) : Installation.Live.Landed seed community cut Reply :=
  Installation.Live.publish paid.round.next.ledger Reply.refused true

def next : St :=
  match step with
  | .ordinary base _ => ⟨base.next, before.amendment⟩
  | .refused _ _ paid _ _ => ⟨{paid.round.next with ledger := (refusal paid).state}, before.amendment⟩
  | .amended _ _ paid _ => ⟨repairedCurrent before.covered paid, some (repair before.covered paid)⟩

def publicReply : Reply :=
  match step with
  | .ordinary base _ => .ordinary base.reply
  | .refused _ _ _ _ _ | .amended _ _ _ _ => .ordinary (.prepaid .ineligible)

def observe : Observation :=
  ⟨before.native.physical.raw.clock, step.next.native.physical.raw.clock, step.publicReply⟩

theorem a_breach_has_one_public_paid_denial
    (breach : paidExposure tariff home orders replies before step.source ≠ ∅) :
    step.observe.reply = .ordinary (.prepaid .ineligible) := by
  cases step with
  | ordinary _ safe => exact (breach safe).elim
  | refused _ _ _ _ _ | amended _ _ _ _ => rfl

theorem same_physical_successor : step.next.native.physical = step.source.next.physical := by
  cases step <;> rfl

theorem same_programme : step.next.native.programme = step.source.next.programme := by
  cases step <;> rfl

theorem same_stack : HEq step.next.native.ledger.stack step.source.next.ledger.stack := by
  cases step <;> rfl

theorem coverage_eq :
    step.next.covered = before.covered ∪ paidExposure tariff home orders replies before step.source := by
  cases step with
  | ordinary base quiet =>
    change before.covered = before.covered ∪ paidExposure tariff home orders replies before base
    rw [quiet, Finset.union_empty]
  | refused wire order paid breach covered =>
    change before.covered = before.covered ∪ witnessed paid
    exact (Finset.union_eq_left.mpr covered).symm
  | amended wire order paid novel => rfl

theorem keeps_coverage : before.covered ⊆ step.next.covered := by
  rw [step.coverage_eq]
  exact Finset.subset_union_left

theorem seals_every_witness :
    paidExposure tariff home orders replies before step.source ⊆ step.next.covered := by
  rw [step.coverage_eq]
  exact Finset.subset_union_right

theorem strictly_extends_iff :
    before.covered ⊂ step.next.covered ↔
      ¬ paidExposure tariff home orders replies before step.source ⊆ before.covered := by
  rw [step.coverage_eq, Finset.ssubset_iff_subset_ne]
  constructor
  · intro strict already
    exact strict.2 (Finset.union_eq_left.mpr already).symm
  · intro novel
    exact ⟨Finset.subset_union_left, fun same =>
      novel (same ▸ Finset.subset_union_right)⟩

end Step

/-- The registered dispatcher supplies the original native receipt.
Only a paid coercive exposure can write a defence amendment. -/
def resolve (base : BaseStep) : Step tariff home orders replies before :=
  match base with
  | .ordinary original unpaid => .ordinary (.ordinary original unpaid) rfl
  | .prepaid wire order paid =>
    if covered : witnessed paid ⊆ before.covered then
      if safe : witnessed paid = ∅ then .ordinary (.prepaid wire order paid) safe else
        .refused wire order paid safe covered
    else .amended wire order paid covered

def advance (due : Slot) : Step tariff home orders replies before :=
  resolve tariff home orders replies before
    (Prepayment.advanceRegistered tariff home orders before.native replies due)

theorem resolve_keeps_the_actual_source (base : BaseStep) :
    (resolve tariff home orders replies before base).source = base := by
  cases base with
  | ordinary _ _ => rfl
  | prepaid wire order paid =>
    by_cases covered : witnessed paid ⊆ before.covered
    · by_cases safe : witnessed paid = ∅
      · simp only [resolve, dif_pos covered, dif_pos safe, Step.source]
      · simp only [resolve, dif_pos covered, dif_neg safe, Step.source]
    · simp only [resolve, dif_neg covered, Step.source]

theorem a_safe_original_visit_is_unchanged (base : BaseStep)
    (safe : paidExposure tariff home orders replies before base = ∅) :
    resolve tariff home orders replies before base = .ordinary base safe := by
  cases base with
  | ordinary _ _ => rfl
  | prepaid wire order paid =>
    change witnessed paid = ∅ at safe
    have covered : witnessed paid ⊆ before.covered := by
      rw [safe]
      exact Finset.empty_subset _
    simp only [resolve, dif_pos covered, dif_pos safe]

theorem a_covered_attack_gets_the_fixed_refusal (wire : Packet) (order : OrderFor wire)
    (paid : PaidReview before.native (bill tariff wire))
    (nonempty : witnessed paid ≠ ∅) (covered : witnessed paid ⊆ before.covered) :
    resolve tariff home orders replies before (.prepaid wire order paid) =
      .refused wire order paid nonempty covered := by
  simp only [resolve, dif_pos covered, dif_neg nonempty]

theorem a_novel_attack_lands_its_amendment (wire : Packet) (order : OrderFor wire)
    (paid : PaidReview before.native (bill tariff wire))
    (novel : ¬ witnessed paid ⊆ before.covered) :
    resolve tariff home orders replies before (.prepaid wire order paid) =
      .amended wire order paid novel := by
  simp only [resolve, dif_neg novel]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace
