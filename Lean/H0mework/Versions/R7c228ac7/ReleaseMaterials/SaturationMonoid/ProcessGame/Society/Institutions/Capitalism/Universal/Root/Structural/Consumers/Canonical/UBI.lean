import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Consumers.Canonical.Support
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.UBI.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Consumers.Canonical.UBI

def input : ProgrammeSource.Input Bool Unit Unit Unit Unit where
  law := Instances.UBI.law
  initial := Instances.UBI.state 0 0
  instructions := Instances.UBI.body

def visit := ProgrammeHistory.visitAt input 1

theorem actual_first_root_interpreted : interpreted input visit := by decide +kernel

theorem actual_first_root_has_no_control : controls input visit = [] :=
  interpreted_word_has_no_unified_control input visit actual_first_root_interpreted

#print axioms actual_first_root_interpreted
#print axioms actual_first_root_has_no_control

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Consumers.Canonical.UBI
