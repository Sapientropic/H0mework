import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Migration.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (small large : List Party) (contained : ∀ person ∈ small, person ∈ large)

include contained

omit [DecidableEq Port] in
private theorem floor_restrict (word : RawEvent Party Good Port Technology Instrument)
    (checked : Material.OriginalNeedFloor input origin current large word) :
    Material.OriginalNeedFloor input origin current small word := by
  intro cell required
  obtain ⟨person, member, occurrence⟩ := List.mem_flatMap.mp required
  exact checked cell (List.mem_flatMap.mpr ⟨person, contained person member, occurrence⟩)

private theorem period_restrict (word : RawEvent Party Good Port Technology Instrument)
    (checked : Material.PeriodChecks input current large word) :
    Material.PeriodChecks input current small word :=
  ⟨checked.1, (fun person member => checked.2.1 person (contained person member)), checked.2.2.1,
    (fun person member => checked.2.2.2.1 person (contained person member)), checked.2.2.2.2⟩

/-- The life scope may be restricted without reclassifying the actors of
the original word: actual self-operation evidence is indexed by its items. -/
theorem renewal_restrict (word : RawEvent Party Good Port Technology Instrument)
    (checked : Material.Migration.RenewalChecks input origin current large word) :
    Material.Migration.RenewalChecks input origin current small word :=
  ⟨period_restrict input current small large contained word checked.1,
    floor_restrict input origin current small large contained word checked.2.1,
    checked.2.2.1, checked.2.2.2⟩

theorem actual_migration_restrict
    (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
    (checked : Actual.Migration.Checks input origin current large pair) :
    Actual.Migration.Checks input origin current small pair :=
  ⟨⟨checked.1.1, (fun person member => checked.1.2.1 person (contained person member)),
      floor_restrict input origin current small large contained pair.1 checked.1.2.2⟩,
    checked.2.1, (fun person member => checked.2.2.1 person (contained person member)),
    renewal_restrict input origin (input.law.next current pair.1) small large contained pair.2 checked.2.2.2⟩

#print axioms renewal_restrict
#print axioms actual_migration_restrict

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census
