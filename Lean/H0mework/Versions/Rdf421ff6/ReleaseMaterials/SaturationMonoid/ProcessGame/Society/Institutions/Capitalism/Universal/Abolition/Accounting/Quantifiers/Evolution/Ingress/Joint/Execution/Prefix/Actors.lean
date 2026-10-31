import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Accounted
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program Innovation Source.ProgrammeFace
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

theorem the_original_actor_cut_is_the_same_completed_source_visit :
    Settlement.committedVisit seed.input seed.depth seed.count =
      (Financial.Installation.observe seed.input (originalCursor seed.input seed.depth seed.count)).completed :=
  Settlement.bookkeeping_recognizes_the_original_observer seed.input seed.depth seed.count
    (an_accounted_original_cause_cannot_execute_a_second_fresh_body seed)

theorem the_public_financial_source_inherits_every_original_generated_actor
    (word : RawEvent Party Good Port Technology Instrument) (party : Party)
    (witness : ActualBirth.Witness seed.input)
    (born : ActualBirth.lookup seed.input
      (Financial.Installation.observe seed.input (originalCursor seed.input seed.depth seed.count)).completed party = some witness) :
    Epoch.Interface.Actors.lookup seed.input seed.depth seed.count (tag seed word) (visit seed word) party =
      some (.original witness) := by
  apply Epoch.Interface.Actors.lookup_retains_original_programme_actor
  unfold Epoch.Actors.oldLookup
  rw [the_original_actor_cut_is_the_same_completed_source_visit]
  exact born

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix
