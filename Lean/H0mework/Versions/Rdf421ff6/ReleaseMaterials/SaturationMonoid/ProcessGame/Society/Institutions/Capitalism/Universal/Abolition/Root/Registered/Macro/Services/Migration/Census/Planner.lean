import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Planner

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : PublicFunction.OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

structure Selection where
  private mk ::
  pair : Material.Migration.CodePair Party Good Port Technology Instrument
  generated : pair ∈ Migration.candidates source depth count prefixLimit renewalLimit current
  checked : Checks source depth count prefixLimit renewalLimit current pair

structure Obstruction where
  private mk ::
  problem : ∀ pair ∈ Migration.candidates source depth count prefixLimit renewalLimit current,
    Problem source depth count prefixLimit renewalLimit current pair

inductive Outcome : Type
  | selected (selection : Selection source depth count prefixLimit renewalLimit current)
  | exhausted (obstruction : Obstruction source depth count prefixLimit renewalLimit current)

def compile : Outcome source depth count prefixLimit renewalLimit current :=
  match Material.inspectList (fun pair => ¬ Checks source depth count prefixLimit renewalLimit current pair)
      (Migration.candidates source depth count prefixLimit renewalLimit current) with
  | .failure pair generated absent => .selected ⟨pair, generated, not_not.mp absent⟩
  | .clear absent => .exhausted ⟨fun pair generated =>
      match inspect source depth count prefixLimit renewalLimit current pair with
      | .accepted checked => False.elim (absent pair generated checked)
      | .refused problem => problem⟩

theorem selects_every_available_current_standing_pair
    (available : ∃ pair ∈ Migration.candidates source depth count prefixLimit renewalLimit current,
      Checks source depth count prefixLimit renewalLimit current pair) :
    ∃ selection, compile source depth count prefixLimit renewalLimit current = .selected selection := by
  cases result : compile source depth count prefixLimit renewalLimit current with
  | selected selection => exact ⟨selection, rfl⟩
  | exhausted obstruction =>
      obtain ⟨pair, generated, checked⟩ := available
      exact ((obstruction.problem pair generated).refutes source depth count prefixLimit renewalLimit current pair checked).elim

theorem Selection.original_command_feed (selection : Selection source depth count prefixLimit renewalLimit current) :
    Actual.Migration.Checks source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw (Actual.members source.input depth count) selection.pair :=
  to_original_actual_migration source depth count prefixLimit renewalLimit current selection.pair selection.checked

#print axioms compile
#print axioms selects_every_available_current_standing_pair
#print axioms Selection.original_command_feed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census
