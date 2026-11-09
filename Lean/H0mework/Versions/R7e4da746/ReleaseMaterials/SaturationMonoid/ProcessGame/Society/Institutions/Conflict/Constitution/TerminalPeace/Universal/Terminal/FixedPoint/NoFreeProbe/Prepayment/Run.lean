import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Dispatch
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Coupling

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
local notation "Command" => ℚ → View → Slot

/-- The coalition can coordinate every input using its full observed
transcript and the ordinary public terms of the present due slot. -/
abbrev AdaptivePolicy (View : Type*) (Party Good Port Technology Instrument : Type) :=
  Nat → List Observation → ℚ → View → Due Party Good Port Technology Instrument

variable (tariff : Tariff Party Good Port Technology Instrument)
  (see : Current (seed := seed) (cut := cut) (community := community) origin people quantum → View)
  (home : AnyAuthoritativeRootCurrent.{0}) (orders : PaymentOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)

def commandedStep (current : State) (input : Command) : Step tariff replies current see home orders :=
  advance tariff replies current see home orders (input current.physical.raw.clock (see current))

def transition (current : State) (input : Command) : State × Observation :=
  let actual := commandedStep tariff see home orders replies current input
  (actual.next, actual.observe)

def publicAgenda (current : State) (input : Command) : View × NoFreeProbe.Observation :=
  (see current, (ordinary tariff replies current (input current.physical.raw.clock (see current)).revision).observation)

def paymentAt (current : State) (input : Command) : Option Packet :=
  (commandedStep tariff see home orders replies current input).paidWire

variable (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum)
  (policy : AdaptivePolicy View Party Good Port Technology Instrument)

def history : Nat → State × List Observation :=
  Erasure.run (transition tariff see home orders replies) opening policy

def stepAt (ordinal : Nat) : Step tariff replies (history tariff see home orders replies opening policy ordinal).1
    see home orders :=
  let before := history tariff see home orders replies opening policy ordinal
  commandedStep tariff see home orders replies before.1 (policy ordinal before.2)

variable (otherReplies : Replies Party Good Port Technology Instrument)
  (other : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

theorem same_public_agenda_selects_the_same_payment (left right : State) (input : Command)
    (observed : publicAgenda tariff see replies left input = publicAgenda tariff see otherReplies right input) :
    paymentAt tariff see home orders replies left input = paymentAt tariff see home orders otherReplies right input := by
  have terms : see left = see right := congrArg Prod.fst observed
  have clock : left.physical.raw.clock = right.physical.raw.clock :=
    congrArg (fun agenda => agenda.2.opensAt) observed
  have command := congrArg₂ input clock terms
  have normal := congrArg (fun agenda => agenda.2.reply) observed
  change (ordinary tariff replies left (input left.physical.raw.clock (see left)).revision).reply =
    (ordinary tariff otherReplies right (input right.physical.raw.clock (see right)).revision).reply at normal
  simp only [paymentAt, commandedStep, charged_wire_is_the_selected_order, selected]
  rw [normal, command, clock, terms]

theorem same_public_agenda_and_no_receipt_give_the_same_observation (left right : State) (input : Command)
    (observed : publicAgenda tariff see replies left input = publicAgenda tariff see otherReplies right input)
    (unpaidLeft : paymentAt tariff see home orders replies left input = none)
    (unpaidRight : paymentAt tariff see home orders otherReplies right input = none) :
    (transition tariff see home orders replies left input).2 =
      (transition tariff see home orders otherReplies right input).2 := by
  have leftQuiet := unpaid_order_is_the_exact_ordinary_write tariff replies left see home orders
    (input left.physical.raw.clock (see left)) unpaidLeft
  have rightQuiet := unpaid_order_is_the_exact_ordinary_write tariff otherReplies right see home orders
    (input right.physical.raw.clock (see right)) unpaidRight
  simp only [transition, commandedStep, leftQuiet, rightQuiet]
  exact congrArg (fun observation : NoFreeProbe.Observation =>
    Observation.mk observation.opensAt observation.landsAt (.ordinary observation.reply)) (congrArg Prod.snd observed)

/-- Match only the original public agenda at commonly observed cuts.
The two hidden states and private qualification callbacks are arbitrary. -/
def SameAgenda : Prop :=
  ∀ n, let left := history tariff see home orders replies opening policy n
    let right := history tariff see home orders otherReplies other policy n
    left.2 = right.2 →
      publicAgenda tariff see replies left.1 (policy n left.2) =
        publicAgenda tariff see otherReplies right.1 (policy n left.2)

private theorem coupled (same : SameAgenda tariff see home orders replies opening policy otherReplies other) (n : Nat)
    (common : (history tariff see home orders replies opening policy n).2 =
      (history tariff see home orders otherReplies other policy n).2) :
    let left := history tariff see home orders replies opening policy n
    let right := history tariff see home orders otherReplies other policy n
    let input := policy n left.2
    publicAgenda tariff see replies left.1 input = publicAgenda tariff see otherReplies right.1 input ∧
      paymentAt tariff see home orders replies left.1 input = paymentAt tariff see home orders otherReplies right.1 input :=
  ⟨same n common, same_public_agenda_selects_the_same_payment tariff see home orders replies otherReplies _ _ _ (same n common)⟩

local notation "L" => history tariff see home orders replies opening policy
local notation "R" => history tariff see home orders otherReplies other policy
local notation "payL" => stepAt tariff see home orders replies opening policy
local notation "payR" => stepAt tariff see home orders otherReplies other policy

theorem unpaid_prefixes_preserve_the_entire_public_transcript
    (same : SameAgenda tariff see home orders replies opening policy otherReplies other)
    (start limit : Nat) (common : (L start).2 = (R start).2)
    (unpaid : ∀ i, start ≤ i → i < limit → (payL i).paidWire = none) :
    (∀ i, start ≤ i → i ≤ limit → (L i).2 = (R i).2) ∧
    (∀ i, start ≤ i → i < limit → (payR i).paidWire = none) :=
  Coupling.before_payment (transition tariff see home orders replies) (transition tariff see home orders otherReplies)
    (paymentAt tariff see home orders replies) (paymentAt tariff see home orders otherReplies)
    (publicAgenda tariff see replies) (publicAgenda tariff see otherReplies) opening other policy
    (coupled tariff see home orders replies opening policy otherReplies other same)
    (same_public_agenda_and_no_receipt_give_the_same_observation tariff see home orders replies otherReplies)
    start limit common unpaid

theorem arbitrarily_many_unpaid_submissions_cannot_separate_the_two_sources
    (same : SameAgenda tariff see home orders replies opening policy otherReplies other)
    (start : Nat) (common : (L start).2 = (R start).2)
    (unpaid : ∀ i, start ≤ i → (payL i).paidWire = none) :
    ∀ i, start ≤ i → (L i).2 = (R i).2 ∧ (payR i).paidWire = none :=
  Coupling.forever_without_payment (transition tariff see home orders replies) (transition tariff see home orders otherReplies)
    (paymentAt tariff see home orders replies) (paymentAt tariff see home orders otherReplies)
    (publicAgenda tariff see replies) (publicAgenda tariff see otherReplies) opening other policy
    (coupled tariff see home orders replies opening policy otherReplies other same)
    (same_public_agenda_and_no_receipt_give_the_same_observation tariff see home orders replies otherReplies)
    start common unpaid

theorem the_first_new_distinction_has_two_actual_prepayments
    (same : SameAgenda tariff see home orders replies opening policy otherReplies other)
    (n : Nat) (common : (L n).2 = (R n).2) (different : (L (n + 1)).2 ≠ (R (n + 1)).2) :
    ∃ wire, (payL n).paidWire = some wire ∧ (payR n).paidWire = some wire :=
  Coupling.first_divergence_pays_on_both (transition tariff see home orders replies)
    (transition tariff see home orders otherReplies)
    (paymentAt tariff see home orders replies) (paymentAt tariff see home orders otherReplies)
    (publicAgenda tariff see replies) (publicAgenda tariff see otherReplies) opening other policy
    (coupled tariff see home orders replies opening policy otherReplies other same)
    (same_public_agenda_and_no_receipt_give_the_same_observation tariff see home orders replies otherReplies)
    n common different

theorem locate_the_first_paid_distinction
    (same : SameAgenda tariff see home orders replies opening policy otherReplies other)
    (start limit : Nat) (within : start ≤ limit) (common : (L start).2 = (R start).2)
    (different : (L limit).2 ≠ (R limit).2) :
    ∃ n, start ≤ n ∧ n < limit ∧
      (∀ i, start ≤ i → i ≤ n → (L i).2 = (R i).2) ∧ (L (n + 1)).2 ≠ (R (n + 1)).2 ∧
      ∃ wire, (payL n).paidWire = some wire ∧ (payR n).paidWire = some wire :=
  Coupling.locate_first_divergence (transition tariff see home orders replies)
    (transition tariff see home orders otherReplies)
    (paymentAt tariff see home orders replies) (paymentAt tariff see home orders otherReplies)
    (publicAgenda tariff see replies) (publicAgenda tariff see otherReplies) opening other policy
    (coupled tariff see home orders replies opening policy otherReplies other same)
    (same_public_agenda_and_no_receipt_give_the_same_observation tariff see home orders replies otherReplies)
    start limit within common different

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
