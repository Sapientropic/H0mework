import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Dispatch
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Erasure
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Closure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)
local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "Slot" => Due Party Good Port Technology Instrument

/-- All the coalition's choices may depend on its entire visible
transcript. The due ordinal is independent of how many messages arrive. -/
abbrev CoalitionPolicy (Party Good Port Technology Instrument : Type) :=
  Nat → List Observation → Due Party Good Port Technology Instrument

variable (tariff : Tariff Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))

def transition (current : State) (due : Slot) : State × Observation :=
  let actual := advance tariff replies current due
  (actual.next, actual.observation)

def history (policy : CoalitionPolicy Party Good Port Technology Instrument) : Nat → State × List Observation :=
  Erasure.run (transition (seed := seed) (cut := cut) (community := community)
    (origin := origin) (people := people) (quantum := quantum) (reserveBase := reserveBase) tariff replies) opening policy

def stepAt (policy : CoalitionPolicy Party Good Port Technology Instrument) (ordinal : Nat) :
    Step tariff replies (history tariff replies opening policy ordinal).1 :=
  let prior := history tariff replies opening policy ordinal
  advance tariff replies prior.1 (policy ordinal prior.2)

def withoutZero (due : Slot) : Slot := by
  classical
  exact { due with packets := due.packets.filter fun wire => decide (¬ ZeroTender wire) }

theorem advance_erases_zero_tenders (current : State) (due : Slot) :
    advance tariff replies current (withoutZero due) = advance tariff replies current due := by
  classical
  refine advance_depends_only_on_the_selected_admitted_wire tariff replies current (withoutZero due) due rfl ?_
  simp only [withoutZero, select]
  apply Erasure.findSome_filter_of_rejected
  intro wire failed
  have zero : ZeroTender wire := by simpa using failed
  exact (checked_eq_none_iff tariff replies current wire).mpr
    (zero_tender_cannot_be_admitted tariff replies current wire zero)

theorem any_adaptive_zero_tenders_erase_from_the_whole_trace
    (policy : CoalitionPolicy Party Good Port Technology Instrument) :
    history tariff replies opening (fun n seen => withoutZero (policy n seen)) =
      history tariff replies opening policy := by
  apply Erasure.run_eq_of_same_effect_along
  intro n
  dsimp only [transition]
  rw [advance_erases_zero_tenders]

theorem arbitrary_adaptive_insertions_of_refused_packets_preserve_the_whole_trace
    (base presented : CoalitionPolicy Party Good Port Technology Instrument)
    (same : ∀ n, let reached := history tariff replies opening base n
      (base n reached.2).revision = (presented n reached.2).revision ∧
      Erasure.InsertsRefused (checked tariff replies reached.1)
        (base n reached.2).packets (presented n reached.2).packets) :
    history tariff replies opening base = history tariff replies opening presented := by
  apply Erasure.run_eq_of_same_effect_along
  intro n
  let reached := history tariff replies opening base n
  change transition tariff replies reached.1 (base n reached.2) =
    transition tariff replies reached.1 (presented n reached.2)
  have writes := advance_depends_only_on_the_selected_admitted_wire tariff replies reached.1
    (base n reached.2) (presented n reached.2) (same n).1 (Erasure.first_stutter (same n).2).symm
  unfold transition
  rw [writes]

theorem two_coalitions_with_the_same_paid_lane_have_the_same_clock_and_replies
    (left right : CoalitionPolicy Party Good Port Technology Instrument)
    (same : ∀ n seen, withoutZero (left n seen) = withoutZero (right n seen)) :
    history tariff replies opening left = history tariff replies opening right := by
  rw [← any_adaptive_zero_tenders_erase_from_the_whole_trace tariff replies opening left,
    ← any_adaptive_zero_tenders_erase_from_the_whole_trace tariff replies opening right]
  exact congrArg (history tariff replies opening) (funext fun n => funext (same n))

abbrev PresentationPolicy (Party Good Port Technology Instrument : Type) :=
  Nat → List Observation → Nat → Wire Party Good Port Technology Instrument

def concurrentHistory (policy : CoalitionPolicy Party Good Port Technology Instrument)
    (traffic : PresentationPolicy Party Good Port Technology Instrument) :
    Nat → State × List Observation :=
  Erasure.run (fun current (arrival : Slot × (Nat → Packet)) => transition tariff replies current arrival.1)
    opening (fun n seen => (policy n seen, traffic n seen))

/-- The presentation stream can be infinite even within one due
ordinal. Each such stream gets the same reply and the original scheduler
has exactly the same state, clocks, and replies. -/
theorem arbitrary_parallel_presentations_have_no_effect
    (policy : CoalitionPolicy Party Good Port Technology Instrument)
    (left right : PresentationPolicy Party Good Port Technology Instrument) :
    concurrentHistory tariff replies opening policy left = history tariff replies opening policy ∧
    concurrentHistory tariff replies opening policy right = history tariff replies opening policy ∧
    (∀ n seen i, present (left n seen i) = present (right n seen i)) :=
  ⟨Erasure.run_ignores_parallel_traffic (transition tariff replies) opening policy left,
    Erasure.run_ignores_parallel_traffic (transition tariff replies) opening policy right, fun _ _ _ => rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe
