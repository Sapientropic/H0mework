import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Productive.Accumulation
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation.Actual (ReceiptAnswers Script)
open Runtime.Viability (Move)

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {answers : ReceiptAnswers seed}
  {registered : Script Party Good Port Technology Instrument → Prop}
  {offers : ProductionMenu Party Good Port Technology Instrument}
  {word : Script Party Good Port Technology Instrument}

/-- An accepted accumulating pilot gives the terminal its exact replay,
with the same pilot as its first native write. -/
noncomputable def realize_accumulating_pilot
    (allowed : Occurrence.Unbounded.Allowed answers loss registered word)
    (ready : ReadyEntry loss word) (choice : ProductionChoice offers)
    (approved : ProductionApproved seed loss word choice)
    (pilot : Move (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice)
      (endAt seed (Occurrence.history loss ++ word)).raw)
    (starts : ProductionStartsWith choice pilot.word) {quantum : ℚ}
    (law : pilot.AccumulationLaw quantum) :
    Realization loss answers registered word offers :=
  ⟨allowed, ready, choice, approved, pilot.accumulatingTrajectory law, starts⟩

theorem viable_entry_from_accumulating_pilot
    (allowed : Occurrence.Unbounded.Allowed answers loss registered word)
    (ready : ReadyEntry loss word) (choice : ProductionChoice offers)
    (approved : ProductionApproved seed loss word choice)
    (pilot : Move (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice)
      (endAt seed (Occurrence.history loss ++ word)).raw)
    (starts : ProductionStartsWith choice pilot.word) {quantum : ℚ}
    (law : pilot.AccumulationLaw quantum) :
    ViableEntry loss answers registered word offers :=
  ⟨allowed, ready, choice, approved, pilot, starts, pilot.accumulation_restarts law⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
