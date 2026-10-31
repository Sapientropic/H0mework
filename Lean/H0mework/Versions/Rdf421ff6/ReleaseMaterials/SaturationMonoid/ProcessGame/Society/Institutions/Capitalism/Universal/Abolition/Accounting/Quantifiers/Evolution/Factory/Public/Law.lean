import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Context
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

def law : RawLaw Party Good Port Technology Instrument := PublicFunction.physicalLaw (Context.readLaw current)

def effectiveAt (phase : Bool) : RawLaw Party Good Port Technology Instrument × List Party :=
  if phase then (law current,Context.readMembers current) else Context.readContext current

theorem the_change_retains_all_other_source_rules :
    law current = { Context.readLaw current with allowed := fun _ _ _ => true,policy := .unrestricted } := rfl

theorem every_port_is_public (technology : Technology) (port : Port) (person : Party) :
    (law current).allowed technology port person = true := rfl

theorem there_is_no_policy_veto : (law current).policy = .unrestricted := rfl

theorem the_physical_source_is_unchanged :
    (law current).technique = (Context.readLaw current).technique ∧
    (law current).revisionCost = (Context.readLaw current).revisionCost ∧
    (law current).settlementUnit = (Context.readLaw current).settlementUnit ∧
    (law current).settlementRate = (Context.readLaw current).settlementRate ∧
    (law current).necessities = (Context.readLaw current).necessities ∧
    (law current).mandatoryMaintenance = (Context.readLaw current).mandatoryMaintenance :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
