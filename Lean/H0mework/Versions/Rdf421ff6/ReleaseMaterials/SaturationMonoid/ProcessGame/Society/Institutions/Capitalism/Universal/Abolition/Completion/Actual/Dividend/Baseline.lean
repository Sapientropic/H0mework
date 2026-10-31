import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend.Trace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- The old source evolves from its frozen admission seed. Public syntax
never enters this baseline; the actual public trace supplies only a horizon. -/
def baselineWords (seed : RawCurrent Party Good Technology Instrument) :
    Nat → List (RawEvent Party Good Port Technology Instrument)
  | 0 => []
  | periods + 1 =>
      ProgrammeSource.wordAt input seed ::
        baselineWords (input.law.next seed (ProgrammeSource.wordAt input seed)) periods

def baselineFinal (seed : RawCurrent Party Good Technology Instrument) (periods : Nat) :=
  Material.Dividend.final input.law seed (baselineWords input seed periods)

def baselineCells (seed : RawCurrent Party Good Technology Instrument) (periods : Nat) :=
  Material.Dividend.cells input.law seed (baselineWords input seed periods)

def baselineNet (seed : RawCurrent Party Good Technology Instrument) (periods : Nat) :=
  Material.Dividend.net input.law seed (baselineWords input seed periods)

theorem the_frozen_old_source_retains_its_exact_material_balance
    (seed : RawCurrent Party Good Technology Instrument) (periods : Nat) (person : Party) (good : Good) :
    (baselineFinal input seed periods).stock person good =
      seed.stock person good + baselineNet input seed periods person good :=
  Material.Dividend.final_stock_is_exact_net input.law seed _ person good

#print axioms baselineWords
#print axioms the_frozen_old_source_retains_its_exact_material_balance

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend
