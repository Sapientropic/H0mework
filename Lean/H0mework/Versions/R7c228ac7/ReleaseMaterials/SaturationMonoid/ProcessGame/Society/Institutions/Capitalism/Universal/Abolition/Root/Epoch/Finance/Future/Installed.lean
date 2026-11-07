import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Transport
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Advance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count sourceDepth sourceCount : Nat)

abbrev frame := Financial.Installation.Runtime.frames input sourceDepth sourceCount
abbrev shape := Installation.Generated.shape input sourceDepth sourceCount
abbrev base := (shape input sourceDepth sourceCount).world input depth count
abbrev initial := Legacy.generated input depth count ((frame input sourceDepth sourceCount).cursor input).account

variable {current : ResponsibilityState (vocabulary input depth count)}
  (run : (process input depth count).Run (initial input depth count sourceDepth sourceCount).current current)
  (account : (process input depth count).GeneratedState)
  (tail : Nonempty ((process input depth count).Run current account.current))

include run tail in
theorem nativeTail : Nonempty ((process input depth count).Run
    (initial input depth count sourceDepth sourceCount).current account.current) :=
  tail.map fun later => run.concatRuns (process input depth count) later

def support := Future.support input depth count (base input depth count sourceDepth sourceCount)
  (initial input depth count sourceDepth sourceCount)
  ((shape input sourceDepth sourceCount).support input depth count (frame input sourceDepth sourceCount).visit.current
    account (nativeTail input depth count sourceDepth sourceCount run account tail)) run account tail

def owner := Future.owner input depth count (base input depth count sourceDepth sourceCount)
  (initial input depth count sourceDepth sourceCount) _
  ((shape input sourceDepth sourceCount).currentOwner input depth count (frame input sourceDepth sourceCount).visit.current
    account (nativeTail input depth count sourceDepth sourceCount run account tail)) run account tail

theorem all_original_and_new_rows_read_one_account :
    (shape input sourceDepth sourceCount).AllRead input depth count account
      (Future.originalRestriction input depth count (base input depth count sourceDepth sourceCount)
        (initial input depth count sourceDepth sourceCount) run
        (support input depth count sourceDepth sourceCount run account tail)) ∧
    Future.AllNewRowsRead input depth count (base input depth count sourceDepth sourceCount)
      (initial input depth count sourceDepth sourceCount) account run
      (support input depth count sourceDepth sourceCount run account tail) := by
  constructor
  · rw [support, Future.original_restriction_is_the_same_installed_support]
    exact (shape input sourceDepth sourceCount).ready_support_reads_one_whole_account input depth count _
      (Installation.Generated.all_registered_rows_are_at_the_actual_current input sourceDepth sourceCount) _ _
  · exact Future.all_new_rows_read_the_same_computed_account input depth count _ _ _ _ _ _

def itemEvolution (item : ActualItem input depth count) :=
  Future.itemEvolution input depth count (base input depth count sourceDepth sourceCount)
    (initial input depth count sourceDepth sourceCount)
    ((shape input sourceDepth sourceCount).continueItemEvolution input depth count _
      (Installation.Generated.all_registered_rows_are_at_the_actual_current input sourceDepth sourceCount)
      account (nativeTail input depth count sourceDepth sourceCount run account tail) item)
    ((shape input sourceDepth sourceCount).currentOwner input depth count _ account
      (nativeTail input depth count sourceDepth sourceCount run account tail)) run account tail item

#print axioms all_original_and_new_rows_read_one_account
#print axioms itemEvolution

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed
