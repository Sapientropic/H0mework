import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

def ordinary : NativeFrame input depth count prefixLimit renewalLimit oldPast start where
  N := world
  anchor := anchor
  family := family
  V := Source.V input depth count prefixLimit renewalLimit oldPast start family
  root := Source.livingRoot input depth count prefixLimit renewalLimit oldPast start family
  occurrence_eq_emitted := Source.occurrence_eq_emitted input depth count prefixLimit renewalLimit oldPast start family
  cursor := some
  support_exact := by
    intro current actual aligned
    cases Option.some.inj aligned
    rfl
  successor := Source.successor input depth count prefixLimit renewalLimit oldPast start family
  cursor_next := by
    intro current actual aligned
    cases Option.some.inj aligned
    exact congrArg some (Source.successor_current input depth count prefixLimit renewalLimit oldPast start family current)
  successor_destination := by
    intro current actual aligned
    cases Option.some.inj aligned
    exact Source.successor_destination_heq input depth count prefixLimit renewalLimit oldPast start family current
  entries_finite := fun current => family.entries_finite current.account current.native
  successor_keys := Source.successor_keys input depth count prefixLimit renewalLimit oldPast start family

#print axioms ordinary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Frame
