import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Declaration
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census.Restriction

import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Census
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Candidates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

abbrev OriginalTask := { task : PublicFunction.PublicTaskSpec Party Good //
  taskOfPayload (originalPayload input (Settlement.committedVisit input depth count).current) = some task }

def rawAt (current : Physical.Cursor Party Good Port Technology Instrument) :=
  (Physical.stateAt input depth count prefixLimit renewalLimit current.past).raw

def standing (current : Physical.Cursor Party Good Port Technology Instrument) :=
  Epoch.Interface.Actors.Census.parties input depth count prefixLimit renewalLimit current

variable (current : Physical.Cursor Party Good Port Technology Instrument)
  (task : OriginalTask input depth count)
  (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)

/-- Raw task bearers and candidate incidences add obligations to the check;
only the actual census is claimed to have already generated M0 standing. -/
def scope := (standing input depth count prefixLimit renewalLimit current ++
  task.val.slots.map PublicFunction.ServiceSlot.bearer ++
  Source.ProgrammeFace.parties input.law (rawAt input depth count prefixLimit renewalLimit current, pair.1) ++
  Source.ProgrammeFace.parties input.law
    (input.law.next (rawAt input depth count prefixLimit renewalLimit current) pair.1, pair.2)).dedup

theorem every_actual_member_remains_in_scope (person : Party)
    (present : person ∈ standing input depth count prefixLimit renewalLimit current) :
    person ∈ scope input depth count prefixLimit renewalLimit current task pair := by
  simp only [scope, List.mem_dedup, List.mem_append]
  exact Or.inl (Or.inl (Or.inl present))

theorem every_original_member_remains_in_scope (person : Party)
    (present : person ∈ Actual.members input depth count) :
    person ∈ scope input depth count prefixLimit renewalLimit current task pair :=
  every_actual_member_remains_in_scope input depth count prefixLimit renewalLimit current task pair person
    (List.mem_dedup.mpr (List.mem_append_left _ present))

def MigrationChecks : Prop := Actual.Migration.Checks input (Actual.origin input depth count)
  (rawAt input depth count prefixLimit renewalLimit current)
  (scope input depth count prefixLimit renewalLimit current task pair) pair

theorem checked_pair_feeds_the_original_compiler
    (checked : MigrationChecks input depth count prefixLimit renewalLimit current task pair) :
    Actual.Migration.Checks input (Actual.origin input depth count)
      (rawAt input depth count prefixLimit renewalLimit current) (Actual.members input depth count) pair :=
  Macro.Services.Migration.Census.actual_migration_restrict input _ _ _ _
    (every_original_member_remains_in_scope input depth count prefixLimit renewalLimit current task pair) pair checked

def candidates := Abolition.Material.Migration.sourcePairs input
  (rawAt input depth count prefixLimit renewalLimit current) prefixLimit renewalLimit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.checked_pair_feeds_the_original_compiler
