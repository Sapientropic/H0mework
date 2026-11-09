import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.Payment
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.PublicWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory.Privacy

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "St" => Resident seed cut community origin people quantum
local notation "CommandAt" => Command Party Good Port Technology Instrument
local notation "PublicTerms" => Terms Party Good Port Technology Instrument
local notation "Readout" => PublicTerms × AdaptivePeace.Observation

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
  (catalogue : Catalogue Party Good Port Technology Instrument)
  (before : Resident seed cut community origin people quantum)

def refreshAgenda : PublicTerms × NoFreeProbe.Observation :=
  (Prepayment.registeredTerms before.2.current,
    ⟨before.2.current.physical.raw.clock, announcedClock before, .renewed⟩)

/-- The reply is announced on the pre-refresh resident. Any new funding
terms belong to the later, actually executed production write. -/
def agenda : CommandAt → PublicTerms × NoFreeProbe.Observation
  | .scheduled input => Runtime.publicAgenda replies before.2 input
  | .refresh => refreshAgenda before

private def ordinary (signal : PublicTerms × NoFreeProbe.Observation) : Readout :=
  (signal.1, ⟨signal.2.opensAt, signal.2.landsAt, .ordinary (.ordinary signal.2.reply)⟩)

def receipt : CommandAt → Option (Wire Party Good Port Technology Instrument)
  | .scheduled input => (Runtime.source home replies before.2 input).source.paidWire
  | .refresh => none

def transition (command : CommandAt) : St × Readout :=
  let after := (advance home replies before catalogue command).next
  let signal := agenda replies before command
  (after, match command with
  | .scheduled input => (signal.1, (Runtime.source home replies before.2 input).observe)
  | .refresh => ordinary signal)

variable (otherReplies : Replies Party Good Port Technology Instrument)
  (other : Resident seed cut community origin people quantum)

theorem refresh_acknowledgements_factor_through_the_prewrite_agenda
    (same : refreshAgenda before = refreshAgenda other) :
    (transition home replies catalogue before .refresh).2 =
      (transition home otherReplies catalogue other .refresh).2 :=
  congrArg ordinary same

theorem refresh_acknowledgement_reports_the_actual_due_clock :
    (transition home replies catalogue before .refresh).2.2.landsAt =
      (advance home replies before catalogue .refresh).next.2.current.physical.raw.clock :=
  (the_refresh_lands_at_its_announced_clock home replies before catalogue).symm

/-- New funding terms are a public material release. A difference in
that release comes from the two literal paid production writes. -/
theorem different_new_terms_require_different_actual_production
    (sameBefore : refreshAgenda before = refreshAgenda other)
    (different : Prepayment.registeredTerms (advance home replies before catalogue .refresh).next.2.current ≠
      Prepayment.registeredTerms (advance home otherReplies other catalogue .refresh).next.2.current) :
    let l := advance home replies before catalogue .refresh
    let r := advance home otherReplies other catalogue .refresh
    l.paid.read.effect.isAccepted = true ∧ r.paid.read.effect.isAccepted = true ∧
      l.paid.read.commands ≠ r.paid.read.commands := by
  intro l r
  obtain ⟨_, leftLaw, leftWord⟩ := refresh_releases_only_the_actual_paid_word home replies before catalogue
  obtain ⟨_, rightLaw, rightWord⟩ := refresh_releases_only_the_actual_paid_word home otherReplies other catalogue
  have sameLaw := congrArg (fun signal : PublicTerms × NoFreeProbe.Observation => signal.1.1) sameBefore
  refine ⟨l.paid.accepted, r.paid.accepted, fun equal => different ?_⟩
  change (l.next.2.current.programme.law, l.next.2.current.recipe.move.word) =
    (r.next.2.current.programme.law, r.next.2.current.recipe.move.word)
  exact Prod.ext ((congrArg (fun p => p.law) leftLaw).trans (sameLaw.trans (congrArg (fun p => p.law) rightLaw).symm))
    (leftWord.trans (equal.trans rightWord.symm))

private theorem quiet (command : CommandAt)
    (same : agenda replies before command = agenda otherReplies other command)
    (unpaid : receipt home replies before command = none)
    (otherUnpaid : receipt home otherReplies other command = none) :
    (transition home replies catalogue before command).2 = (transition home otherReplies catalogue other command).2 := by
  cases command with
  | refresh => exact congrArg ordinary same
  | scheduled input =>
    change ((Runtime.publicAgenda replies before.2 input).1, (Runtime.source home replies before.2 input).observe) =
      ((Runtime.publicAgenda otherReplies other.2 input).1, (Runtime.source home otherReplies other.2 input).observe)
    rw [Runtime.unpaid_observation_is_the_original_agenda home replies before.2 input unpaid,
      Runtime.unpaid_observation_is_the_original_agenda home otherReplies other.2 input otherUnpaid]
    exact congrArg ordinary same

variable (strategy : Nat → List (Terms Party Good Port Technology Instrument × AdaptivePeace.Observation) →
  Command Party Good Port Technology Instrument)

def history : Nat → St × List Readout := Erasure.run (transition home replies catalogue) before strategy

local notation "L" => history home replies catalogue before strategy
local notation "R" => history home otherReplies catalogue other strategy

private def actualPolicy (n : Nat) (_ : St) : CommandAt :=
  strategy n (L n).2

private theorem reached_state (n : Nat) :
    (L n).1 = RebaseHistory.history home replies catalogue before
      (actualPolicy home replies catalogue before strategy) n := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    change (advance home replies (L n).1 catalogue (strategy n (L n).2)).next = _
    change _ = (advance home replies
      (RebaseHistory.history home replies catalogue before (actualPolicy home replies catalogue before strategy) n)
      catalogue (strategy n (L n).2)).next
    rw [earlier]

def SameAgendas : Prop :=
  ∀ n, (L n).2 = (R n).2 →
    agenda replies (L n).1 (strategy n (L n).2) =
      agenda otherReplies (R n).1 (strategy n (L n).2)

variable (agendas : SameAgendas home replies catalogue before otherReplies other strategy)
  (signed : SameSignedReads before.2 other.2)
  (context : SameReserveContext (leftBase := before.1) (rightBase := other.1))

include agendas signed context

private theorem matched (n : Nat) (common : (L n).2 = (R n).2) :
    let command := strategy n (L n).2
    agenda replies (L n).1 command = agenda otherReplies (R n).1 command ∧
      receipt home replies (L n).1 command = receipt home otherReplies (R n).1 command := by
  intro command
  have same := agendas n common
  refine ⟨same, ?_⟩
  cases literal : command with
  | refresh => rfl
  | scheduled input =>
    have observed : Runtime.publicAgenda replies (L n).1.2 input = Runtime.publicAgenda otherReplies (R n).1.2 input := by
      change agenda replies (L n).1 command = agenda otherReplies (R n).1 command at same
      rw [literal] at same
      exact same
    have left := reached_state home replies catalogue before strategy n
    have right := reached_state home otherReplies catalogue other strategy n
    have keptL := every_interleaving_keeps_the_original_rows_and_orders home replies catalogue before
      (actualPolicy home replies catalogue before strategy) n
    have keptR := every_interleaving_keeps_the_original_rows_and_orders home otherReplies catalogue other
      (actualPolicy home otherReplies catalogue other strategy) n
    have floorL := original_reserve_coordinates home replies catalogue before (actualPolicy home replies catalogue before strategy) n
    have floorR := original_reserve_coordinates home otherReplies catalogue other (actualPolicy home otherReplies catalogue other strategy) n
    rw [← left] at keptL floorL
    rw [← right] at keptR floorR
    exact same_public_agenda_selects_payment_after_rebase home replies otherReplies (L n).1.2 (R n).1.2 input
      ⟨keptL.2.1.trans (signed.tariff.trans keptR.2.1.symm),
       keptL.2.2.1.trans (signed.payment.trans keptR.2.2.1.symm),
       keptL.2.2.2.1.trans (signed.proposal.trans keptR.2.2.2.1.symm)⟩
      ⟨floorL.2.1.trans (context.claims.trans floorR.2.1.symm),
       floorL.2.2.trans (context.technology.trans floorR.2.2.symm),
       fun p g => (context.leftStock p g).trans (floorL.1 p g),
       fun p g => (context.rightStock p g).trans (floorR.1 p g)⟩ observed

/-- Every unpaid prefix has the same public transcript and due clock
across both histories, including when their reserve indices differ. -/
theorem every_unpaid_mixed_prefix_keeps_the_observation (start limit : Nat) (common : (L start).2 = (R start).2)
    (unpaid : ∀ i, start ≤ i → i < limit → receipt home replies (L i).1 (strategy i (L i).2) = none) :
    (∀ i, start ≤ i → i ≤ limit → (L i).2 = (R i).2) ∧
      (∀ i, start ≤ i → i < limit → receipt home otherReplies (R i).1 (strategy i (R i).2) = none) :=
  Prepayment.Coupling.before_payment (transition home replies catalogue) (transition home otherReplies catalogue)
    (receipt home replies) (receipt home otherReplies) (agenda replies) (agenda otherReplies)
    before other strategy (matched home replies catalogue before otherReplies other strategy agendas signed context)
    (fun l r input => quiet home replies catalogue l otherReplies r input) start limit common unpaid

theorem a_distinction_in_the_mixed_history_requires_the_same_actual_bill (n : Nat)
    (common : (L n).2 = (R n).2) (different : (L (n + 1)).2 ≠ (R (n + 1)).2) :
    ∃ wire, receipt home replies (L n).1 (strategy n (L n).2) = some wire ∧
      receipt home otherReplies (R n).1 (strategy n (R n).2) = some wire :=
  Prepayment.Coupling.first_divergence_pays_on_both (transition home replies catalogue) (transition home otherReplies catalogue)
    (receipt home replies) (receipt home otherReplies) (agenda replies) (agenda otherReplies)
    before other strategy (matched home replies catalogue before otherReplies other strategy agendas signed context)
    (fun l r input => quiet home replies catalogue l otherReplies r input) n common different

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory.Privacy
