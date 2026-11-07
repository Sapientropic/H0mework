import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Trace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Baseline
import Mathlib.Data.List.Dedup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

def seed := Physical.stateAt input depth count prefixLimit renewalLimit oldPast
def publicCurrent := Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast current.past

def horizon :=
  (publicCurrent input depth count prefixLimit renewalLimit oldPast current).raw.round -
    (seed input depth count prefixLimit renewalLimit oldPast).raw.round

def oldEndpoint := baselineFinal input (seed input depth count prefixLimit renewalLimit oldPast).raw
  (horizon input depth count prefixLimit renewalLimit oldPast current)

def comparisonCells : List (Party × Good) :=
  (baselineCells input (seed input depth count prefixLimit renewalLimit oldPast).raw
      (horizon input depth count prefixLimit renewalLimit oldPast current) ++
    traceCells input (seed input depth count prefixLimit renewalLimit oldPast) current.past).dedup

def delta (person : Party) (good : Good) : ℚ :=
  traceNet input (seed input depth count prefixLimit renewalLimit oldPast) current.past person good -
    baselineNet input (seed input depth count prefixLimit renewalLimit oldPast).raw
      (horizon input depth count prefixLimit renewalLimit oldPast current) person good

theorem the_dividend_is_the_actual_public_stock_minus_its_frozen_reference (person : Party) (good : Good) :
    delta input depth count prefixLimit renewalLimit oldPast current person good =
      (publicCurrent input depth count prefixLimit renewalLimit oldPast current).raw.stock person good -
        (oldEndpoint input depth count prefixLimit renewalLimit oldPast current).stock person good := by
  have actual := actual_prefix_stock_is_exactly_its_complete_net_flow input
    (seed input depth count prefixLimit renewalLimit oldPast) current.past person good
  have old := the_frozen_old_source_retains_its_exact_material_balance input
    (seed input depth count prefixLimit renewalLimit oldPast).raw
    (horizon input depth count prefixLimit renewalLimit oldPast current) person good
  change (publicCurrent input depth count prefixLimit renewalLimit oldPast current).raw.stock person good = _ at actual
  change (oldEndpoint input depth count prefixLimit renewalLimit oldPast current).stock person good = _ at old
  rw [actual, old]
  unfold delta
  ring

theorem no_unlisted_bearer_or_good_has_a_hidden_dividend (person : Party) (good : Good)
    (absent : (person, good) ∉ comparisonCells input depth count prefixLimit renewalLimit oldPast current) :
    delta input depth count prefixLimit renewalLimit oldPast current person good = 0 := by
  have outside :
      (person, good) ∉ baselineCells input (seed input depth count prefixLimit renewalLimit oldPast).raw
        (horizon input depth count prefixLimit renewalLimit oldPast current) ∧
      (person, good) ∉ traceCells input (seed input depth count prefixLimit renewalLimit oldPast) current.past := by
    simpa only [comparisonCells, List.mem_dedup, List.mem_append, not_or] using absent
  unfold delta
  rw [no_prefix_effect_is_outside_the_actual_affected_cells input _ _ person good outside.2]
  have old := Material.Dividend.no_effect_outside_actual_cells input.law
    (seed input depth count prefixLimit renewalLimit oldPast).raw
    (baselineWords input (seed input depth count prefixLimit renewalLimit oldPast).raw
      (horizon input depth count prefixLimit renewalLimit oldPast current)) person good outside.1
  change baselineNet input _ _ person good = 0 at old
  rw [old, sub_self]

#print axioms the_dividend_is_the_actual_public_stock_minus_its_frozen_reference
#print axioms no_unlisted_bearer_or_good_has_a_hidden_dividend

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend
