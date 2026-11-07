import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count sourceDepth sourceCount : Nat)

theorem owner_responsibility_is_the_same_original_row
    {current : ResponsibilityState (vocabulary input depth count)}
    (run : (process input depth count).Run (initial input depth count sourceDepth sourceCount).current current)
    (left : (process input depth count).GeneratedState)
    (leftNative : Nonempty ((process input depth count).Run current left.current))
    (right : (process input depth count).GeneratedState)
    (rightNative : Nonempty ((process input depth count).Run current right.current)) :
    (owner input depth count sourceDepth sourceCount run left leftNative).1 =
      (owner input depth count sourceDepth sourceCount run right rightNative).1 := by
  unfold owner
  rw [Keys.owner_key_is_the_original_lift, Keys.owner_key_is_the_original_lift]
  apply congrArg (Keys.liftResponsibility input depth count (base input depth count sourceDepth sourceCount)
    (initial input depth count sourceDepth sourceCount) run)
  exact Keys.actual_frame_owner_key input depth count _ _ left _ right _

#print axioms owner_responsibility_is_the_same_original_row

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed
