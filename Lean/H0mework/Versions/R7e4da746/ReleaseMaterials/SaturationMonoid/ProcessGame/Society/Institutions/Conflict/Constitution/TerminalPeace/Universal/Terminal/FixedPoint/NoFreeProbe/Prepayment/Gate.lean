import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Budget
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Admission

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

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum
local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "Bill" => ReviewBid Party Good Port Technology Instrument

/-- Original personal authorizations to spend at this due time. Their
input is the literal bill. Qualification has a separate, paid reader. -/
abbrev PaymentOrders (Party Good Port Technology Instrument : Type) :=
  ℚ → ReviewBid Party Good Port Technology Instrument → Party → Bool

/-- The registered production law and literal productive word are
available as funding terms. A coarser observer can use the whole fibre. -/
def registeredTerms (current : State) :
    RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument :=
  (current.programme.law, current.recipe.move.word)

variable {View : Type*}
  (see : Current (seed := seed) (cut := cut) (community := community) origin people quantum → View)

/-- Uniform spendability is calculated on the actual source laws in the
whole observation fibre. No private eligibility callback enters it. -/
def UniformBudget (visible : View) (now : ℚ) (bid : Bill) : Prop :=
  ∀ other : State, see other = visible → other.physical.raw.clock = now →
    BaseBudget other.programme.law cut.raw other.recipe.move.word bid

theorem a_budget_failure_has_a_same_observation_witness {visible : View} {now : ℚ} {bid : Bill}
    (failed : ¬ UniformBudget see visible now bid) :
    ∃ other : State, see other = visible ∧ other.physical.raw.clock = now ∧
      ¬ BaseBudget other.programme.law cut.raw other.recipe.move.word bid := by
  classical
  by_contra absent
  apply failed
  intro other observed stamped
  by_contra blocked
  exact absent ⟨other, observed, stamped, blocked⟩

theorem uniform_registered_budget_iff (current : State) (bid : Bill) :
    UniformBudget (registeredTerms (seed := seed) (cut := cut) (community := community)
      (origin := origin) (people := people) (quantum := quantum))
      (registeredTerms current) current.physical.raw.clock bid ↔
      BaseBudget current.programme.law cut.raw current.recipe.move.word bid := by
  constructor
  · intro funded
    exact funded current rfl rfl
  · intro funded other terms _
    have law := congrArg Prod.fst terms
    have word := congrArg Prod.snd terms
    change other.programme.law = current.programme.law at law
    change other.recipe.move.word = current.recipe.move.word at word
    rw [law, word]
    exact funded

variable (tariff : Tariff Party Good Port Technology Instrument)
  (home : AnyAuthoritativeRootCurrent.{0}) (orders : PaymentOrders Party Good Port Technology Instrument)

/-- The home is the installed payment anchor. It stays fixed as
qualification replies generate new resident currents. -/
structure CanPrepay (visible : View) (now : ℚ) (wire : Packet) : Prop where
  scope : wire.home = home
  stamp : wire.clock = now
  screened : fundingScreen tariff wire = true
  standing : wire.payer ∈ people
  ownOrder : orders now (bill tariff wire) wire.payer = true
  budget : UniformBudget see visible now (bill tariff wire)

def inspectOrder (visible : View) (now : ℚ) (wire : Packet) :
    Option { packet : Packet // CanPrepay see tariff home orders visible now packet } := by
  classical
  exact if fundingScreen tariff wire then
    if accepted : CanPrepay see tariff home orders visible now wire then some ⟨wire, accepted⟩ else none
  else none

theorem inspectOrder_none_iff (visible : View) (now : ℚ) (wire : Packet) :
    inspectOrder see tariff home orders visible now wire = none ↔
      ¬ CanPrepay see tariff home orders visible now wire := by
  classical
  by_cases accepted : CanPrepay see tariff home orders visible now wire
  · simp [inspectOrder, accepted, accepted.screened]
  · simp [inspectOrder, accepted]

def selectOrder (visible : View) (now : ℚ) (wires : List Packet) :
    Option { packet : Packet // CanPrepay see tariff home orders visible now packet } :=
  wires.findSome? (inspectOrder see tariff home orders visible now)

theorem absent_personal_order_erases (visible : View) (now : ℚ) (wire : Packet)
    (absent : orders now (bill tariff wire) wire.payer = false) :
    inspectOrder see tariff home orders visible now wire = none := by
  apply (inspectOrder_none_iff see tariff home orders visible now wire).mpr
  intro found
  rw [found.ownOrder] at absent
  contradiction

theorem stale_order_erases (visible : View) (now : ℚ) (wire : Packet) (stale : wire.clock < now) :
    inspectOrder see tariff home orders visible now wire = none :=
  (inspectOrder_none_iff see tariff home orders visible now wire).mpr fun found => (ne_of_lt stale) found.stamp

theorem a_zero_tender_is_erased_before_funding (visible : View) (now : ℚ) (wire : Packet)
    (free : ZeroTender wire) :
    inspectOrder see tariff home orders visible now wire = none := by
  classical
  simp [inspectOrder, zero_tender_stops_before_the_current_is_read tariff wire free]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
