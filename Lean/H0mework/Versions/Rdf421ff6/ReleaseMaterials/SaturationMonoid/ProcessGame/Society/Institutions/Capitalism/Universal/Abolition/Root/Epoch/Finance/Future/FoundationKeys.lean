import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.InstalledFoundation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Foundation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem inheritedEntry_key {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (left right : (World.folded input depth count (ProgrammeSource.N input) run).Support) :
    (inheritedEntry input depth count run left).1 = (inheritedEntry input depth count run right).1 := by
  induction run with
  | nil => cases left <;> cases right <;> rfl
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact congrArg Sum.inl (inherited left.1 right.1)
      | cross slot obligation present boundary => exact inherited left right
      | reopen _ _ _ impossible => exact impossible.elim

theorem actualEntry_key {native : Financial.Installation.NativeFrame input}
    (shape : Installation.Shape input native) (left right : (shape.world input depth count).Support) :
    (actualEntry input depth count shape left).1 = (actualEntry input depth count shape right).1 := by
  induction shape with
  | base start positive => exact inheritedEntry_key input depth count start.account.generated left right
  | born prior registered inherited => exact congrArg Sum.inl (inherited left.1 right.1)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Foundation

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count sourceDepth sourceCount : Nat)

theorem canonicalEntry_key {current : ResponsibilityState (vocabulary input depth count)}
    (run : (process input depth count).Run (initial input depth count sourceDepth sourceCount).current current)
    (left right : (Future.world input depth count (base input depth count sourceDepth sourceCount)
      (initial input depth count sourceDepth sourceCount) run).Support) :
    (canonicalEntry input depth count sourceDepth sourceCount run left).1 =
      (canonicalEntry input depth count sourceDepth sourceCount run right).1 := by
  induction run with
  | nil => exact Foundation.actualEntry_key input depth count _ left right
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact congrArg Sum.inl (inherited left.1 right.1)
      | cross slot obligation present boundary => exact inherited left right
      | reopen _ _ _ impossible => exact impossible.elim

#print axioms canonicalEntry_key

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed
