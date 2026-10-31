import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Replay
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (claim : Responsibility.Family.Claim mechanism past nature response)

def priorityPast (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim) :
    List (RawEvent Party Good Port Technology Instrument) →
      List (Compile.RawInput Party Good Port Technology Instrument)
  | [] => []
  | proposal :: remaining =>
      .execute (publicReencoded input (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw
        (Priority.Root.Gate.executableWord claim frame proposal)) ::
      priorityPast (Priority.Root.Installation.successor claim frame proposal) remaining

theorem the_actual_priority_history_generates_its_own_public_representation
    (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (inputs : List (RawEvent Party Good Port Technology Instrument))
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (sameRaw : before.raw = (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw)
    (sameLaw : frame.actualLaw = Physical.Public.interpreter input) :
    ((priorityPast input claim frame inputs).foldl
      (fun current raw => (Physical.Public.compile input current raw).next) before).raw =
      (Abolition.Accounting.Root.Reentry.Frame.state claim (Priority.Root.afterInputs claim frame inputs)).raw := by
  induction inputs generalizing frame before with
  | nil => exact sameRaw
  | cons proposal remaining later =>
    simp only [priorityPast,List.foldl_cons,Priority.Root.afterInputs]
    apply later
    · have actual := public_reencoded_reads_the_same_original_next input before
        (Priority.Root.Gate.executableWord claim frame proposal)
      rw [sameRaw] at actual
      rw [actual,← sameLaw]
      exact (Priority.Root.Installation.actual_next_runs_the_original_physical_law_on_the_entire_accepted_prefix
        claim frame proposal).symm
    · exact sameLaw

theorem every_representation_step_is_the_original_accepted_prefix
    (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (proposal : RawEvent Party Good Port Technology Instrument) :
    (publicReencoded input (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw
      (Priority.Root.Gate.executableWord claim frame proposal)).length =
        (Priority.Root.Gate.executableWord claim frame proposal).length :=
  Functions.Replay.replay_keeps_every_original_instruction_position _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix
