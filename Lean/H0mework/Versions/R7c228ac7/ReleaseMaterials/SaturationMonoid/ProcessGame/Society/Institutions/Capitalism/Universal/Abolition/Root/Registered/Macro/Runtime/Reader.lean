import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

theorem reference_next_keeps_the_same_raw_reader : frame.next.package.reader = frame.package.reader := by
  unfold Frame.next
  cases selected : frame.query with
  | internal work =>
      change frame.internalNext.package.reader = _
      unfold Frame.internalNext
      split <;> rfl
  | raw germ => rfl

#print axioms reference_next_keeps_the_same_raw_reader

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
