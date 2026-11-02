import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Search
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend.Order

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (prefixLimit renewalLimit : Nat)

abbrev P := Plan input origin current members prefixLimit renewalLimit

def candidates : List (P input origin current members prefixLimit renewalLimit) :=
  (sourcePairs input current prefixLimit renewalLimit).attach.filterMap fun code =>
    inspectPlan input origin current members prefixLimit renewalLimit code.val code.property

theorem candidates_cover_every_checked_source_pair
    (pair : CodePair Party Good Port Technology Instrument)
    (original : pair ∈ sourcePairs input current prefixLimit renewalLimit)
    (checked : PairChecks input origin current members pair) :
    ∃ plan ∈ candidates input origin current members prefixLimit renewalLimit, plan.pair = pair := by
  obtain ⟨plan, produced, same⟩ := inspectPlan_returns_exactly_the_checked_source_code input origin current members
    prefixLimit renewalLimit pair original checked
  refine ⟨plan, ?_, same⟩
  apply List.mem_filterMap.mpr
  exact ⟨⟨pair, original⟩, List.mem_attach _ _, produced⟩

def Better (first last : P input origin current members prefixLimit renewalLimit) : Prop :=
  Dividend.Checks input.law current [first.pair.1, first.pair.2] [last.pair.1, last.pair.2]

instance (first last : P input origin current members prefixLimit renewalLimit) :
    Decidable (Better input origin current members prefixLimit renewalLimit first last) := by
  unfold Better
  infer_instance

theorem better_transitive {first middle last : P input origin current members prefixLimit renewalLimit}
    (earlier : Better input origin current members prefixLimit renewalLimit first middle)
    (later : Better input origin current members prefixLimit renewalLimit middle last) :
    Better input origin current members prefixLimit renewalLimit first last :=
  Dividend.checks_transitive input.law current earlier later

theorem better_irreflexive (plan : P input origin current members prefixLimit renewalLimit) :
    ¬ Better input origin current members prefixLimit renewalLimit plan plan :=
  Dividend.checks_irreflexive input.law current _

#print axioms candidates_cover_every_checked_source_pair
#print axioms better_transitive

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred
