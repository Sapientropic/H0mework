import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Capital
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

def originalBody (nature : RequestAt) (opponent : Response) (current : Current) :=
  if current.round = 1 then capitalWord
  else if current.round = 2 then word false nature opponent
  else []

def originalInput (nature : RequestAt) (opponent : Response) :
    ProgrammeSource.Input Party Good Bool Nat Unit where
  law := law
  initial := genesis
  instructions := []
  emission? := some (originalBody nature opponent)
  localAttempts := fun _ => commonWork ++ [discovery 0,discovery 1,discovery 2]
  observedEmission? := some
    { generate := fun current => .original current (originalBody nature opponent current)
      word := ProgrammeSource.ProgrammeReport.word }

def actualExecution (nature : RequestAt) (opponent : Response) (index : Nat) :=
  (ProgrammeLiving.projectionLaw (originalInput nature opponent)).project .execution
    (ProgrammeSource.emitted (originalInput nature opponent)
      (ProgrammeHistory.visitAt (originalInput nature opponent) index).current) ()

theorem the_original_source_starts_with_zero_financial_claims
    (nature : RequestAt) (opponent : Response) :
    (originalInput nature opponent).initial.claims = fun _ _ _ => 0 := rfl

theorem the_capital_prefix_is_on_the_original_actual_occurrence
    (nature : RequestAt) (opponent : Response) :
    (actualExecution nature opponent 1).before = start ∧
      (actualExecution nature opponent 1).submitted = capitalWord := ⟨rfl,rfl⟩

theorem the_original_capital_relation_is_generated_before_the_future_trial
    (nature : RequestAt) (opponent : Response) :
    Nonempty (Source.ProgrammeControl.Kernel.CapitalRelationKernel law
      (actualExecution nature opponent 1).before (actualExecution nature opponent 1).submitted) :=
  ⟨originalCapital⟩

theorem the_trial_seed_is_the_actual_successor_of_the_capital_occurrence
    (nature : RequestAt) (opponent : Response) :
    (actualExecution nature opponent 1).after = seed ∧
      (actualExecution nature opponent 2).before = seed := ⟨rfl,rfl⟩

theorem the_controlled_trial_is_the_original_source_execution
    (nature : RequestAt) (opponent : Response) :
    (actualExecution nature opponent 2).submitted = word false nature opponent ∧
      (actualExecution nature opponent 2).interpreted = execution false nature opponent ∧
      (actualExecution nature opponent 2).after = law.next seed (word false nature opponent) := ⟨rfl,rfl,rfl⟩

theorem the_actual_source_consumes_its_original_execution_ledger_and_next
    (nature : RequestAt) (opponent : Response) :
    type_of% (ProgrammeHistory.execution_face_shares_whole_ledger_and_next
      (originalInput nature opponent) 2) :=
  ProgrammeHistory.execution_face_shares_whole_ledger_and_next (originalInput nature opponent) 2

theorem every_actual_discovery_and_response_has_its_source_cost_decomposition
    (nature : RequestAt) (opponent : Response) (good : Good) :
    controlLoss law openLaw (actualExecution nature opponent 2).interpreted.items
        (execution true nature opponent).items good =
      (output openLaw (execution true nature opponent).items good -
        output law (actualExecution nature opponent 2).interpreted.items good) -
      (cost openLaw (execution true nature opponent).items good -
        cost law (actualExecution nature opponent 2).interpreted.items good) := by
  rw [the_controlled_trial_is_the_original_source_execution nature opponent |>.2.1]
  exact control_loss_is_foregone_output_after_all_additional_costs _ _ _ _ _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario
