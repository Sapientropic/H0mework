import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Readout
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Actual

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

def datum : Macro.Ingress.Datum input 0 0 where
  reader := fun _ => .primitive Control.Scenario.ownerPresent

abbrev current (nature : RequestAt) (tick : Nat) :=
  Macro.Runtime.actualFrame (review := none) input 0 0 datum 0 0 (reader nature) tick

def boundaryTick (nature : RequestAt) : Nat → Nat
  | 0 => Macro.Runtime.internalBoundaryTick (review := none) input 0 0 datum 0 0 (reader nature) 0
  | index + 1 => Macro.Runtime.internalBoundaryTick (review := none) input 0 0 datum 0 0 (reader nature)
      (boundaryTick nature index + 1)

abbrev boundary (nature : RequestAt) (index : Nat) := current nature (boundaryTick nature index)

theorem every_boundary_is_visited_by_the_same_original_engine
    (nature : RequestAt) (index : Nat) :
    (Macro.Runtime.run (review := none) input 0 0 datum 0 0 (reader nature) (boundaryTick nature index + 1)).engine.node =
      .active (boundary nature index).presentation :=
  Macro.Runtime.run_is_the_original_registered_history (review := none) input 0 0 datum 0 0 (reader nature) _

theorem every_scheduled_attempt_has_the_original_whole_root_and_next
    (nature : RequestAt) (index : Nat) :
    type_of% (Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := none)
      input 0 0 datum 0 0 (reader nature)
      (Macro.Runtime.run (review := none) input 0 0 datum 0 0 (reader nature) (boundaryTick nature index + 1))) :=
  Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := none) input 0 0 datum 0 0 (reader nature) _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
