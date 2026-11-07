import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}

theorem actual_history_keeps_the_same_effective_interpreter
    (claim : Responsibility.Family.Claim mechanism past nature response)
    (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    (Priority.Root.afterInputs claim frame inputs).actualLaw = frame.actualLaw := by
  induction inputs generalizing frame with
  | nil => rfl
  | cons word rest later => exact (later (Priority.Root.Installation.successor claim frame word)).trans rfl

variable [DecidableEq Port]
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

theorem the_source_current_reads_the_original_public_interpreter :
    seed.current.actualLaw = Physical.Public.interpreter seed.input :=
  actual_history_keeps_the_same_effective_interpreter seed.claim (baseFrame seed) seed.inputs

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix
