import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "History" => Script Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument

theorem the_joint_successor_keeps_every_original_loss_and_the_crossed_horizon
    (installed : Emergency.Installed seed base scope) (community : Party → Community)
    (past suffix : History) (crossed : scope.task.deadline < (endAt seed past).raw.clock) :
    let written := publishAfter (run seed community past) suffix
    let cut := endAt seed (past ++ suffix)
    Quantities.Recorded seed (past ++ suffix) ∧
    (∀ origin ∈ originalLosses seed community past,
      ∃ balance, ∃ row, written.next.read row = .inr (origin, balance)) ∧
    Emergency.Installed cut base scope ∧ scope.task.deadline < cut.raw.clock ∧
    ∀ word : Word, ∀ command : ActualCommand base scope cut.raw word,
      command.command ≠ .accept ∧ command.command ≠ .renew ∧
      ∀ holder, command.command ≠ .propose holder := by
  dsimp only
  refine ⟨(publishAfter (run seed community past) suffix).recorded, ?_, ?_⟩
  · exact publication_keeps_every_previous_loss seed community past suffix
  · exact Emergency.no_authority_after_a_crossing installed past suffix crossed

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
