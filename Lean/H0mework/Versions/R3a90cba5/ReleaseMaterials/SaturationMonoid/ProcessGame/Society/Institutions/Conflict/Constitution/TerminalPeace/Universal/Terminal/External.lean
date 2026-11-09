import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Queue
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Entry

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual (ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (registered : Script Party Good Port Technology Instrument → Prop)

variable {loss answers registered} {word : Script Party Good Port Technology Instrument}
  {offers : ProductionMenu Party Good Port Technology Instrument}

theorem Realization.every_exact_cofinal_external_future_crosses_the_same_terminal
    (run : Realization loss answers registered word offers)
    (external : External.Trace Runtime.Current (Runtime.Write Party Good Port Technology Instrument))
    (starts : external.current 0 = Runtime.currentAt (Occurrence.reached answers loss word)
      run.programme (originalRaw loss) run.people run.menus 0)
    (localChecks : ∀ n, external.Check
      (Runtime.currentAt (Occurrence.reached answers loss word) run.programme (originalRaw loss)
        run.people run.menus)
      (Runtime.writeAt (Occurrence.reached answers loss word) run.programme (originalRaw loss)
        run.people run.menus) n)
    (clock : ∀ bound, ∃ visit, bound < (external.current visit).2) :
    let original := Occurrence.reached answers loss word
    (∃! factor, external.Factors
      (Runtime.currentAt original run.programme (originalRaw loss) run.people run.menus)
      (Runtime.writeAt original run.programme (originalRaw loss) run.people run.menus) factor) ∧
      ∃! visit, external.FirstAt 1 visit ∧
        (external.current visit).1 = (Runtime.run original run.programme
          (originalRaw loss) run.people run.menus 0).state.resident.erase := by
  let original := Occurrence.reached answers loss word
  let observed := Runtime.currentAt original run.programme (originalRaw loss) run.people run.menus
  let writes := Runtime.writeAt original run.programme (originalRaw loss) run.people run.menus
  have factor := external.factor_of_checks observed writes starts localChecks
  have complete : external.Progress := external.progress_of_clock_cofinal Prod.snd factor
    (Runtime.clock_mono original run.programme (originalRaw loss) run.people run.menus) clock
  exact ⟨(external.exact_local_checks_iff_unique_factor observed writes).mp ⟨starts, localChecks⟩,
    Runtime.every_complete_external_presentation_crosses_the_same_first_whole_write original
      run.programme (originalRaw loss) run.people run.menus external factor complete⟩

/-- Neutral external traffic may have any finite width at each due
visit. The original write itself supplies progress beyond that queue. -/
def Realization.queuedPresentation (run : Realization loss answers registered word offers) (queue : Nat → Nat) :=
  let original := Occurrence.reached answers loss word
  External.Queue.presentation queue
    (Runtime.currentAt original run.programme (originalRaw loss) run.people run.menus)
    (Runtime.writeAt original run.programme (originalRaw loss) run.people run.menus)

theorem Realization.arbitrary_finite_queues_preserve_the_compulsory_paid_entry
    (run : Realization loss answers registered word offers) (queue : Nat → Nat) :
    let original := Occurrence.reached answers loss word
    let external := run.queuedPresentation queue
    (∀ start bound, ∃ visit ≥ start, bound < (external.current visit).2) ∧
    ∃! visit, external.FirstAt 1 visit ∧
      (external.current visit).1 = (Runtime.run original run.programme
        (originalRaw loss) run.people run.menus 0).state.resident.erase := by
  let original := Occurrence.reached answers loss word
  let observed := Runtime.currentAt original run.programme (originalRaw loss) run.people run.menus
  let writes := Runtime.writeAt original run.programme (originalRaw loss) run.people run.menus
  let external := run.queuedPresentation queue
  have factor : external.Factors observed writes external.ordinal :=
    External.Queue.presentation_uses_only_the_original_writes queue observed writes
  have progress : external.Progress :=
    External.Queue.every_finite_queue_schedule_progresses queue observed writes
  exact ⟨(Runtime.cofinal_external_time_iff_complete_original_progress original run.programme
      (originalRaw loss) run.people run.menus external factor run.clock).mp progress,
    Runtime.every_complete_external_presentation_crosses_the_same_first_whole_write original
      run.programme (originalRaw loss) run.people run.menus external factor progress⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
