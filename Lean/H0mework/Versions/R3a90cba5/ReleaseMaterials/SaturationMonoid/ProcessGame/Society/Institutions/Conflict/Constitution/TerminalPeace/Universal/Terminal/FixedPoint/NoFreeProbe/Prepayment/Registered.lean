import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Finitary
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Run

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
  {reserveBase : RawCurrent Party Good Technology Instrument}

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)
local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "Slot" => Due Party Good Port Technology Instrument
local notation "Terms" => RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument
local notation "seeTerms" => (registeredTerms (seed := seed) (cut := cut) (community := community)
  (origin := origin) (people := people) (quantum := quantum) (reserveBase := reserveBase))

variable (tariff : Tariff Party Good Port Technology Instrument)
  (home : AnyAuthoritativeRootCurrent.{0}) (orders : PaymentOrders Party Good Port Technology Instrument)
  (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))

private def FundingReady (wire : Packet) : Prop :=
  fundingScreen tariff wire = true ∧ wire.home = home ∧ wire.clock = current.physical.raw.clock ∧
    wire.payer ∈ people ∧ orders current.physical.raw.clock (bill tariff wire) wire.payer = true ∧
    budgetCheck current.programme.law reserveBase current.recipe.move.word (bill tariff wire) = true

private theorem ready_iff (wire : Packet) :
    FundingReady tariff home orders current wire ↔
      CanPrepay seeTerms tariff home orders (registeredTerms current) current.physical.raw.clock wire := by
  have budget := (budgetCheck_iff current.programme.law reserveBase current.recipe.move.word (bill tariff wire)).trans
    (uniform_registered_budget_iff current (bill tariff wire)).symm
  constructor
  · rintro ⟨screen, atHome, stamp, standing, ownOrder, funded⟩
    exact ⟨atHome, stamp, screen, standing, ownOrder, budget.mp funded⟩
  · intro accepted
    exact ⟨accepted.screened, accepted.scope, accepted.stamp, accepted.standing, accepted.ownOrder,
      budget.mpr accepted.budget⟩

/-- At a registered recipe, source spendability is calculated by a
finite scan of its actual material support and the quoted expense. -/
def inspectRegistered (wire : Packet) :
    Option { w : Packet // CanPrepay seeTerms tariff home orders (registeredTerms current) current.physical.raw.clock w } := by
  letI : Decidable (wire.home = home) := Classical.propDecidable _
  letI : Decidable (FundingReady tariff home orders current wire) := by
    unfold FundingReady
    infer_instance
  exact if ready : FundingReady tariff home orders current wire then
    some ⟨wire, (ready_iff tariff home orders current wire).mp ready⟩
  else none

theorem registered_check_is_the_exact_fibre_check (wire : Packet) :
    inspectRegistered tariff home orders current wire =
      inspectOrder seeTerms tariff home orders (registeredTerms current) current.physical.raw.clock wire := by
  classical
  by_cases paid : CanPrepay seeTerms tariff home orders (registeredTerms current) current.physical.raw.clock wire
  · have ready := (ready_iff tariff home orders current wire).mpr paid
    simp [inspectRegistered, inspectOrder, ready, paid.screened, paid]
  · have denied : ¬ FundingReady tariff home orders current wire :=
      fun ready => paid ((ready_iff tariff home orders current wire).mp ready)
    rw [(inspectOrder_none_iff seeTerms tariff home orders (registeredTerms current) current.physical.raw.clock wire).mpr paid]
    simp [inspectRegistered, denied]

variable (replies : Replies Party Good Port Technology Instrument)

def advanceRegistered (due : Slot) : Step tariff replies current seeTerms home orders :=
  let chosen :=
    if (ordinary tariff replies current due.revision).reply = .revised then none else
      due.packets.findSome? (inspectRegistered tariff home orders current)
  writeSelected tariff replies current seeTerms home orders due chosen

theorem registered_dispatch_is_the_exact_private_dispatch (due : Slot) :
    advanceRegistered tariff home orders current replies due = advance tariff replies current seeTerms home orders due := by
  have checks := funext (registered_check_is_the_exact_fibre_check tariff home orders current)
  simp only [advanceRegistered, advance, selected, selectInAgenda, selectOrder, checks]

variable (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (policy : AdaptivePolicy
    (RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
    Party Good Port Technology Instrument)

def registeredHistory : Nat → State × List Observation :=
  Erasure.run (fun current (command : ℚ → Terms → Slot) =>
    let step := advanceRegistered tariff home orders current replies
      (command current.physical.raw.clock (registeredTerms current))
    (step.next, step.observe)) opening policy

theorem registered_run_is_the_exact_private_history :
    registeredHistory tariff home orders replies opening policy =
      history tariff seeTerms home orders replies opening policy := by
  unfold registeredHistory history
  congr 1
  funext current command
  simp only [registered_dispatch_is_the_exact_private_dispatch, transition, commandedStep]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
