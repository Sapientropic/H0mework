import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Privacy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (home : AnyAuthoritativeRootCurrent.{0})
  (replies otherReplies : Replies Party Good Port Technology Instrument)
  (initial other : State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase))
  (policy : Policy Party Good Port Technology Instrument)

local notation "L" => history home replies initial policy
local notation "R" => history home otherReplies other policy
local notation "lInput" n => inputAt home replies initial policy n
local notation "rInput" n => inputAt home otherReplies other policy n
local notation "lVisit" n => source home replies (L n).1 (lInput n)
local notation "rVisit" n => source home otherReplies (R n).1 (rInput n)

def CommonObservations (n : Nat) : Prop :=
  (L n).2 = (R n).2 ∧ (L n).1.base.language = (R n).1.base.language

/-- Compare at the same public due signal, even when the private
qualification callbacks and actual material reserves above the base differ. -/
def SameAgendas : Prop :=
  ∀ n, CommonObservations home replies otherReplies initial other policy n →
    publicAgenda replies (L n).1 (lInput n) = publicAgenda otherReplies (R n).1 (rInput n)

local notation "Common" n => CommonObservations home replies otherReplies initial other policy n

variable (agendas : SameAgendas home replies otherReplies initial other policy)
  (reads : SameReads initial other)

include agendas reads

theorem common_observation_selects_the_same_order (n : Nat) (common : Common n) :
    (lVisit n).source.paidWire = (rVisit n).source.paidWire ∧
    ((lVisit n).source.paidWire = none → Common (n + 1)) := by
  have observed := agendas n common
  have terms := congrArg Prod.fst observed
  have clock := congrArg (fun agenda => agenda.2.opensAt) observed
  change Prepayment.registeredTerms (L n).1.current = Prepayment.registeredTerms (R n).1.current at terms
  change (L n).1.current.physical.raw.clock = (R n).1.current.physical.raw.clock at clock
  have input : (lInput n) = (rInput n) := by
    change policy n (L n).2 (L n).1.current.physical.raw.clock
      (Prepayment.registeredTerms (L n).1.current) (L n).1.base.language =
      policy n (R n).2 (R n).1.current.physical.raw.clock
        (Prepayment.registeredTerms (R n).1.current) (R n).1.base.language
    rw [common.1, clock, terms, common.2]
  have signedL := history_keeps_original_signatures home replies initial policy n
  have signedR := history_keeps_original_signatures home otherReplies other policy n
  have signed : SameReads (L n).1 (R n).1 :=
    ⟨signedL.1.trans (reads.tariff.trans signedR.1.symm),
      signedL.2.1.trans (reads.orders.trans signedR.2.1.symm),
      signedL.2.2.trans (reads.proposals.trans signedR.2.2.symm)⟩
  rw [← input] at observed
  have selected := same_public_agenda_selects_the_same_payment home replies otherReplies
    (L n).1 (R n).1 (lInput n) signed observed
  have exactPayment : (lVisit n).source.paidWire = (rVisit n).source.paidWire := by
    rw [← input]
    exact selected
  refine ⟨exactPayment, fun unpaid => ⟨?_, ?_⟩⟩
  · have same : (lVisit n).observe = (rVisit n).observe := by
      rw [← input]
      rw [unpaid_observation_is_the_original_agenda home replies (L n).1 (lInput n) unpaid,
        unpaid_observation_is_the_original_agenda home otherReplies (R n).1 (lInput n) (selected.symm.trans unpaid),
        observed]
    change (lVisit n).observe :: (L n).2 = (rVisit n).observe :: (R n).2
    rw [same, common.1]
  · rw [history_succ, history_succ, unpaid_keeps_the_language home replies _ _ unpaid,
      unpaid_keeps_the_language home otherReplies _ _ (exactPayment.symm.trans unpaid)]
    exact common.2

theorem every_unpaid_prefix_keeps_the_transcript_and_language
    (start limit : Nat) (common : Common start)
    (unpaid : ∀ n, start ≤ n → n < limit → (lVisit n).source.paidWire = none) :
    ∀ n, start ≤ n → n ≤ limit → (Common n) ∧
      (n < limit → (rVisit n).source.paidWire = none) := by
  have preserved (elapsed : Nat) : start + elapsed ≤ limit → Common (start + elapsed) := by
    induction elapsed with
    | zero => exact fun _ => common
    | succ n earlier =>
      intro within
      have prior : start + n < limit := lt_of_lt_of_le (Nat.lt_succ_self _) within
      exact (common_observation_selects_the_same_order home replies otherReplies initial other policy agendas reads _
        (earlier prior.le)).2 (unpaid _ (Nat.le_add_right _ _) prior)
  intro n fromStart within
  have same : Common n := by
    rw [← Nat.add_sub_of_le fromStart] at within ⊢
    exact preserved _ within
  exact ⟨same, fun later =>
    (common_observation_selects_the_same_order home replies otherReplies initial other policy agendas reads _
      same).1.symm.trans (unpaid n fromStart later)⟩

theorem a_new_distinction_requires_the_same_actual_payment_on_both_sides (n : Nat)
    (common : Common n) (different : ¬ (Common (n + 1))) :
    ∃ wire, (lVisit n).source.paidWire = some wire ∧ (rVisit n).source.paidWire = some wire := by
  have paid := common_observation_selects_the_same_order home replies otherReplies initial other policy agendas reads n common
  cases recorded : (lVisit n).source.paidWire with
  | none => exact (different (paid.2 recorded)).elim
  | some wire => exact ⟨wire, rfl, paid.1.symm.trans recorded⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
