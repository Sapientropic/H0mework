import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.History

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
  {reserveBase : RawCurrent Party Good Technology Instrument}

local notation "St" => State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)
local notation "Terms" => RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument
local notation "Slot" => NoFreeProbe.Due Party Good Port Technology Instrument
local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "Command" => ℚ → Terms → Slot
local notation "sourceTerms" => (Prepayment.registeredTerms (seed := seed) (cut := cut)
  (community := community) (origin := origin) (people := people) (quantum := quantum) (reserveBase := reserveBase))

variable (tariff : Tariff Party Good Port Technology Instrument) (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument) (replies : Replies Party Good Port Technology Instrument)

def publicAgenda (state : St) (command : Command) : Terms × NoFreeProbe.Observation :=
  Prepayment.publicAgenda tariff sourceTerms replies state.native command

def paymentAt (state : St) (command : Command) : Option Packet :=
  (commandedStep tariff home orders replies state command).source.paidWire

theorem commanded_source_is_the_original_dispatch (state : St) (command : Command) :
    (commandedStep tariff home orders replies state command).source =
      Prepayment.commandedStep tariff sourceTerms home orders replies state.native command := by
  unfold commandedStep advance Prepayment.commandedStep
  rw [resolve_keeps_the_actual_source, Prepayment.registered_dispatch_is_the_exact_private_dispatch]

theorem paymentAt_is_the_original_payment (state : St) (command : Command) :
    paymentAt tariff home orders replies state command =
      Prepayment.paymentAt tariff sourceTerms home orders replies state.native command :=
  congrArg Prepayment.Step.paidWire
    (commanded_source_is_the_original_dispatch tariff home orders replies state command)

theorem commanded_step_keeps_the_ordinary_clocks (state : St) (command : Command) :
    let actual := (commandedStep tariff home orders replies state command).observe
    let scheduled := (publicAgenda tariff replies state command).2
    actual.opensAt = scheduled.opensAt ∧ actual.landsAt = scheduled.landsAt := by
  let step := commandedStep tariff home orders replies state command
  refine ⟨rfl, ?_⟩
  change step.next.native.physical.raw.clock = (publicAgenda tariff replies state command).2.landsAt
  rw [step.same_physical_successor, commanded_source_is_the_original_dispatch]
  exact Prepayment.assessment_uses_the_exact_ordinary_clock tariff replies state.native sourceTerms home orders _

theorem a_paid_observation_has_the_original_receipt (state : St) (command : Command) {wire : Packet}
    (charged : paymentAt tariff home orders replies state command = some wire) :
    ∃ (order : Prepayment.CanPrepay sourceTerms tariff home orders (sourceTerms state.native)
        state.native.physical.raw.clock wire)
      (paid : NoFreeProbe.PaidReview state.native (bill tariff wire)),
      (commandedStep tariff home orders replies state command).source = .prepaid wire order paid := by
  let due := command state.native.physical.raw.clock (sourceTerms state.native)
  have actual : (Prepayment.advance tariff replies state.native sourceTerms home orders due).paidWire = some wire :=
    (paymentAt_is_the_original_payment tariff home orders replies state command).symm.trans charged
  obtain ⟨order, paid, same⟩ := Prepayment.a_selected_order_has_its_own_prepaid_receipt tariff replies state.native
    sourceTerms home orders due actual
  exact ⟨order, paid, (commanded_source_is_the_original_dispatch tariff home orders replies state command).trans same⟩

/-- Unpaid traffic leaves exactly the ordinary due visit, including
its next state and any approved production revision. -/
theorem unpaid_command_is_the_exact_ordinary_write (state : St) (command : Command)
    (unpaid : paymentAt tariff home orders replies state command = none) :
    let due := command state.native.physical.raw.clock (sourceTerms state.native)
    let normal := Prepayment.ordinary tariff replies state.native due.revision
    let uncharged := Prepayment.ordinary_has_no_charge tariff replies state.native due.revision
    commandedStep tariff home orders replies state command = .ordinary (.ordinary normal uncharged) rfl := by
  let due := command state.native.physical.raw.clock (sourceTerms state.native)
  have originalUnpaid : (Prepayment.advance tariff replies state.native sourceTerms home orders due).paidWire = none := by
    rw [paymentAt_is_the_original_payment] at unpaid
    exact unpaid
  have ordinary := Prepayment.unpaid_order_is_the_exact_ordinary_write tariff replies state.native
    sourceTerms home orders due originalUnpaid
  dsimp only
  unfold commandedStep advance
  rw [Prepayment.registered_dispatch_is_the_exact_private_dispatch, ordinary]
  rfl

variable (otherReplies : Replies Party Good Port Technology Instrument)

theorem same_public_agenda_selects_the_same_payment (left right : St) (command : Command)
    (observed : publicAgenda tariff replies left command = publicAgenda tariff otherReplies right command) :
    paymentAt tariff home orders replies left command = paymentAt tariff home orders otherReplies right command := by
  rw [paymentAt_is_the_original_payment, paymentAt_is_the_original_payment]
  exact Prepayment.same_public_agenda_selects_the_same_payment tariff sourceTerms home orders replies otherReplies
    left.native right.native command observed

theorem same_public_agenda_and_no_payment_give_the_same_observation (left right : St) (command : Command)
    (observed : publicAgenda tariff replies left command = publicAgenda tariff otherReplies right command)
    (unpaidLeft : paymentAt tariff home orders replies left command = none)
    (unpaidRight : paymentAt tariff home orders otherReplies right command = none) :
    (transition tariff home orders replies left command).2 =
      (transition tariff home orders otherReplies right command).2 := by
  unfold transition
  rw [unpaid_command_is_the_exact_ordinary_write tariff home orders replies left command unpaidLeft,
    unpaid_command_is_the_exact_ordinary_write tariff home orders otherReplies right command unpaidRight]
  exact congrArg (fun read : NoFreeProbe.Observation =>
    Observation.mk read.opensAt read.landsAt (.ordinary (.ordinary read.reply))) (congrArg Prod.snd observed)

variable (opening other : State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (policy : Policy Party Good Port Technology Instrument)

local notation "L" => history tariff home orders replies opening policy
local notation "R" => history tariff home orders otherReplies other policy
local notation "payL" => (fun n => Prepayment.Step.paidWire (Step.source (stepAt tariff home orders replies opening policy n)))
local notation "payR" => (fun n => Prepayment.Step.paidWire (Step.source (stepAt tariff home orders otherReplies other policy n)))

/-- Coverage and private qualification may differ. The common agenda
uses only the registered funding terms and the actual ordinary due signal. -/
def SameAgenda : Prop :=
  ∀ n, let left := L n
    let right := R n
    left.2 = right.2 →
      publicAgenda tariff replies left.1 (policy n left.2) =
        publicAgenda tariff otherReplies right.1 (policy n left.2)

variable (same : SameAgenda tariff home orders replies otherReplies opening other policy)

include same

private theorem coupled (n : Nat) (common : (L n).2 = (R n).2) :
    let left := L n
    let right := R n
    let command := policy n left.2
    publicAgenda tariff replies left.1 command = publicAgenda tariff otherReplies right.1 command ∧
      paymentAt tariff home orders replies left.1 command = paymentAt tariff home orders otherReplies right.1 command :=
  ⟨same n common,
    same_public_agenda_selects_the_same_payment tariff home orders replies otherReplies _ _ _ (same n common)⟩

theorem unpaid_prefixes_preserve_the_entire_public_transcript (start limit : Nat)
    (common : (L start).2 = (R start).2)
    (unpaid : ∀ i, start ≤ i → i < limit → payL i = none) :
    (∀ i, start ≤ i → i ≤ limit → (L i).2 = (R i).2) ∧
    (∀ i, start ≤ i → i < limit → payR i = none) :=
  Prepayment.Coupling.before_payment (transition tariff home orders replies) (transition tariff home orders otherReplies)
    (paymentAt tariff home orders replies) (paymentAt tariff home orders otherReplies)
    (publicAgenda tariff replies) (publicAgenda tariff otherReplies) opening other policy
    (coupled tariff home orders replies otherReplies opening other policy same)
    (same_public_agenda_and_no_payment_give_the_same_observation tariff home orders replies otherReplies)
    start limit common unpaid

theorem arbitrarily_many_unpaid_submissions_cannot_separate_the_two_sources (start : Nat)
    (common : (L start).2 = (R start).2) (unpaid : ∀ i, start ≤ i → payL i = none) :
    ∀ i, start ≤ i → (L i).2 = (R i).2 ∧ payR i = none :=
  Prepayment.Coupling.forever_without_payment (transition tariff home orders replies)
    (transition tariff home orders otherReplies) (paymentAt tariff home orders replies)
    (paymentAt tariff home orders otherReplies) (publicAgenda tariff replies)
    (publicAgenda tariff otherReplies) opening other policy
    (coupled tariff home orders replies otherReplies opening other policy same)
    (same_public_agenda_and_no_payment_give_the_same_observation tariff home orders replies otherReplies)
    start common unpaid

theorem locate_the_first_paid_distinction (start limit : Nat) (within : start ≤ limit)
    (common : (L start).2 = (R start).2) (different : (L limit).2 ≠ (R limit).2) :
    ∃ n, start ≤ n ∧ n < limit ∧
      (∀ i, start ≤ i → i ≤ n → (L i).2 = (R i).2) ∧ (L (n + 1)).2 ≠ (R (n + 1)).2 ∧
      ∃ wire, payL n = some wire ∧ payR n = some wire :=
  Prepayment.Coupling.locate_first_divergence (transition tariff home orders replies)
    (transition tariff home orders otherReplies) (paymentAt tariff home orders replies)
    (paymentAt tariff home orders otherReplies) (publicAgenda tariff replies)
    (publicAgenda tariff otherReplies) opening other policy
    (coupled tariff home orders replies otherReplies opening other policy same)
    (same_public_agenda_and_no_payment_give_the_same_observation tariff home orders replies otherReplies)
    start limit within common different

omit same in
/-- The old guard answers a covered attack at the paid position itself.
Its refusal and actual successor are independent of qualification. -/
theorem covered_refusal_is_independent_of_qualification (state : St) (wire : Packet)
    (order : Prepayment.CanPrepay sourceTerms tariff home orders (sourceTerms state.native)
      state.native.physical.raw.clock wire)
    (paid : NoFreeProbe.PaidReview state.native (bill tariff wire))
    (breach : witnessed paid ≠ ∅) (covered : witnessed paid ⊆ state.covered) :
    let left := resolve tariff home orders replies state (.prepaid wire order paid)
    let right := resolve tariff home orders otherReplies state (.prepaid wire order paid)
    left.observe = right.observe ∧ left.next = right.next := by
  dsimp only
  rw [a_covered_attack_gets_the_fixed_refusal tariff home orders replies state wire order paid breach covered,
    a_covered_attack_gets_the_fixed_refusal tariff home orders otherReplies state wire order paid breach covered]
  exact ⟨rfl, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace
