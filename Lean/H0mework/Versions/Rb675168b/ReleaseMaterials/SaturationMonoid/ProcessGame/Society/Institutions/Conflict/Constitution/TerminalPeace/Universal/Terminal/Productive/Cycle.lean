import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Productive.Cycle
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Whole

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation.Actual (ReceiptAnswers Script)
open Runtime.Viability (Live Move Path)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {answers : ReceiptAnswers seed}
  {registered : Script Party Good Port Technology Instrument → Prop}
  {offers : ProductionMenu Party Good Port Technology Instrument}
  {word : Script Party Good Port Technology Instrument}

/-- A paid pilot can change the production state before a finite
resource cycle starts. Each cycle opening has its own personal exits. -/
theorem viable_entry_from_paid_pilot_and_cycle
    (allowed : Occurrence.Unbounded.Allowed answers loss registered word)
    (ready : ReadyEntry loss word) (choice : ProductionChoice offers)
    (approved : ProductionApproved seed loss word choice)
    (pilot : Move (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice)
      (endAt seed (Occurrence.history loss ++ word)).raw)
    (starts : ProductionStartsWith choice pilot.word)
    {length : Nat} {finish : RawCurrent Party Good Technology Instrument}
    (cycle : Path (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice) pilot.next length finish)
    (timing : (productionInput seed loss word choice).law.TimeIndependent) (stable : cycle.RetimeStable)
    (nonempty : 0 < length) (closes : finish = pilot.next.retime finish.clock finish.round) :
    ViableEntry loss answers registered word offers :=
  ⟨allowed, ready, choice, approved, pilot, starts, cycle.cycle_is_live timing stable nonempty closes⟩

/-- Whole clearance yields an attained zero of the same optimizer. The
chosen prefix is charged to the original ledger and starts its paid runtime. -/
theorem the_terminal_selects_zero_from_an_actual_whole_payment
    (viable : ViableEntry loss answers registered word offers)
    (all : WholeCleared loss answers word) :
    ∃ selected run minimum fewest,
      source_generated_terminal_peace loss answers registered offers = .attained selected run minimum fewest ∧
      (Occurrence.balance answers loss selected).remaining = 0 := by
  have paid : (Occurrence.balance answers loss word).remaining = 0 :=
    all (loss, Occurrence.balance answers loss word) (Occurrence.balance_is_in_the_reached_rows answers loss word)
  have zero := (full_actual_reparation_and_living_peace_iff_zero_is_attained
    loss answers registered offers).mp ⟨word, ⟨realize viable⟩, paid⟩
  cases source_generated_terminal_peace loss answers registered offers with
  | attained selected run minimum fewest =>
    refine ⟨selected, run, minimum, fewest, rfl, ?_⟩
    have atZero : ((Occurrence.balance answers loss selected).remaining : ℝ) = 0 :=
      minimum.trans zero.1
    exact_mod_cast atZero
  | approached missing _ => exact (missing zero.2).elim
  | obstructed failed _ => exact (failed word ⟨realize viable⟩).elim

/-- The actual experiment writes its original material positions and
keeps every old row on the exact generated successor. -/
theorem Realization.the_pilot_writes_the_whole_original_successor
    (run : Realization loss answers registered word offers) :
    let prior := Occurrence.reached answers loss word
    let first := Runtime.run prior run.programme (originalRaw loss) run.people run.menus 0
    first.state.stack.balances = prior.stack.balances ∧
    (⟨prior.world, (Installation.Core.action prior first.read true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = first.state.resident.erase ∧
    first.read.items = run.programme.law.rawItems
      (endAt seed (Occurrence.history loss ++ word)).raw (run.trajectory.move 0).word ∧
    first.read.after.raw = run.trajectory.state 1 :=
  ⟨Runtime.every_actual_visit_keeps_the_original_rows _ _ _ _ _ 0,
    Runtime.the_first_visit_writes_the_original_whole_next _ _ _ _ _,
    run.pilot_writes_the_actual_material_items⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
