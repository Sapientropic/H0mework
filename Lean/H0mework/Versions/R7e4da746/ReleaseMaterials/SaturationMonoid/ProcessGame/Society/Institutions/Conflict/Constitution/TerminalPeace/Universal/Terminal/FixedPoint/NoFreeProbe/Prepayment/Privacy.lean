import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {View : Type*}

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum
local notation "Slot" => Due Party Good Port Technology Instrument
local notation "Packet" => Wire Party Good Port Technology Instrument

variable (tariff : Tariff Party Good Port Technology Instrument)
  (see : Current (seed := seed) (cut := cut) (community := community) origin people quantum → View)
  (home : AnyAuthoritativeRootCurrent.{0}) (orders : PaymentOrders Party Good Port Technology Instrument)
  (left right : Replies Party Good Port Technology Instrument)

/-- Changing the private qualification alone changes neither the
chosen material debit nor the quiet transition at a common current. -/
theorem private_qualification_cannot_choose_the_payment (current : State) (input : ℚ → View → Slot)
    (sameRevision : left.revision = right.revision) :
    paymentAt tariff see home orders left current input = paymentAt tariff see home orders right current input := by
  apply same_public_agenda_selects_the_same_payment
  unfold publicAgenda ordinary
  rw [sameRevision]

private theorem private_qualification_keeps_the_unpaid_transition (current : State) (input : ℚ → View → Slot)
    (sameRevision : left.revision = right.revision)
    (unpaid : paymentAt tariff see home orders left current input = none) :
    transition tariff see home orders left current input = transition tariff see home orders right current input := by
  have unpaidRight := (private_qualification_cannot_choose_the_payment tariff see home orders left right
    current input sameRevision).symm.trans unpaid
  have leftQuiet := unpaid_order_is_the_exact_ordinary_write tariff left current see home orders
    (input current.physical.raw.clock (see current)) unpaid
  have rightQuiet := unpaid_order_is_the_exact_ordinary_write tariff right current see home orders
    (input current.physical.raw.clock (see current)) unpaidRight
  simp only [transition, commandedStep, leftQuiet, rightQuiet, Step.next, Step.observe, Step.reply, ordinary]
  rw [sameRevision]

variable (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum)
  (policy : AdaptivePolicy View Party Good Port Technology Instrument)

local notation "L" => history tariff see home orders left opening policy
local notation "R" => history tariff see home orders right opening policy
local notation "paidL" => stepAt tariff see home orders left opening policy

/-- At a common opening, no future agenda evidence is needed. Until
the first actual charge, changing the hidden callback keeps the entire
dependent current and transcript equal. -/
theorem changing_only_private_qualification_preserves_every_unpaid_prefix
    (sameRevision : left.revision = right.revision)
    (cutoff : Nat) (unpaid : ∀ i < cutoff, (paidL i).paidWire = none) :
    L cutoff = R cutoff := by
  induction cutoff with
  | zero => rfl
  | succ n earlier =>
    have same := earlier fun i before => unpaid i (Nat.lt_succ_of_lt before)
    let reached := L n
    have quiet := private_qualification_keeps_the_unpaid_transition tariff see home orders left right
      reached.1 (policy n reached.2) sameRevision (unpaid n (Nat.lt_succ_self n))
    change (let step := transition tariff see home orders left reached.1 (policy n reached.2)
            (step.1, step.2 :: reached.2)) =
      (let current := R n
       let step := transition tariff see home orders right current.1 (policy n current.2)
       (step.1, step.2 :: current.2))
    rw [← same, quiet]

abbrev ParallelTraffic (Party Good Port Technology Instrument : Type) :=
  Nat → List Observation → Nat → Wire Party Good Port Technology Instrument

def withParallelTraffic (traffic : ParallelTraffic Party Good Port Technology Instrument) :
    Nat → State × List Observation :=
  Erasure.run
    (fun current (arrivals : (ℚ → View → Slot) × (Nat → Packet)) =>
      transition tariff see home orders left current arrivals.1)
    opening (fun n prior => (policy n prior, traffic n prior))

/-- An arbitrary concurrent stream, including full-looking tenders,
gets only the original presentation receipt and no scheduler slot. -/
theorem parallel_presentations_leave_no_timing_or_qualification_signal
    (first second : ParallelTraffic Party Good Port Technology Instrument) :
    withParallelTraffic tariff see home orders left opening policy first = L ∧
    withParallelTraffic tariff see home orders left opening policy second = L ∧
    ∀ n seen i, present (first n seen i) = present (second n seen i) := by
  have erased (traffic : ParallelTraffic Party Good Port Technology Instrument) :
      withParallelTraffic tariff see home orders left opening policy traffic = L := by
    funext n
    induction n with
    | zero => rfl
    | succ n earlier =>
      exact congrArg (fun prior : State × List Observation =>
        let due := transition tariff see home orders left prior.1 (policy n prior.2)
        (due.1, due.2 :: prior.2)) earlier
  exact ⟨erased first, erased second, fun _ _ _ => rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
