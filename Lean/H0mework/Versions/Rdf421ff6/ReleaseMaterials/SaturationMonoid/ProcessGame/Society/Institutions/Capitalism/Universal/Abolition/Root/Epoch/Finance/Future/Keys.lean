import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Keys

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem inherited_owner_key (base : WorldRelationNetwork) (support : base.Support)
    (owner : OpenResponsibilityAt base support)
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (left : (process input depth count).GeneratedState)
    (leftNative : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (World.OldAccount input run)).current left.current))
    (right : (process input depth count).GeneratedState)
    (rightNative : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (World.OldAccount input run)).current right.current)) :
    (World.currentOwner input depth count base support owner run left leftNative).1 =
      (World.currentOwner input depth count base support owner run right rightNative).1 := by
  induction run with
  | nil => rfl
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact congrArg Sum.inl (inherited
          (World.earlierTail input depth count prior (.admit claim) left leftNative)
          (World.earlierTail input depth count prior (.admit claim) right rightNative))
      | cross slot obligation present boundary =>
        exact inherited
          (World.earlierTail input depth count prior (.cross slot obligation present boundary) left leftNative)
          (World.earlierTail input depth count prior (.cross slot obligation present boundary) right rightNative)
      | reopen _ _ _ impossible => exact impossible.elim

theorem actual_frame_owner_key {native : Financial.Installation.NativeFrame input}
    (shape : Installation.Shape input native) (current : native.V.Current)
    (left : (process input depth count).GeneratedState)
    (leftNative : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (native.cursor current).account).current left.current))
    (right : (process input depth count).GeneratedState)
    (rightNative : Nonempty ((process input depth count).Run
      (Legacy.generated input depth count (native.cursor current).account).current right.current)) :
    (shape.currentOwner input depth count current left leftNative).1 =
      (shape.currentOwner input depth count current right rightNative).1 := by
  induction shape with
  | base start positive => exact inherited_owner_key input depth count _ _ _ _ left _ right _
  | born prior registered inherited =>
      rcases current with ⟨current, event⟩
      cases event <;> exact congrArg Sum.inl (inherited _ leftNative rightNative)

variable (base : WorldRelationNetwork) (initial : (process input depth count).GeneratedState)

def liftResponsibility : {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    base.Responsibility → (Future.world input depth count base initial run).Responsibility
  | _, .nil, key => key
  | _, .step prior (.admit _), key => .inl (liftResponsibility prior key)
  | _, .step prior (.cross _ _ _ _), key => liftResponsibility prior key
  | _, .step _ (.reopen _ _ _ impossible), _ => impossible.elim

theorem owner_key_is_the_original_lift (support : base.Support) (owner : OpenResponsibilityAt base support)
    {current : ResponsibilityState (vocabulary input depth count)}
    (run : (process input depth count).Run initial.current current)
    (account : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run current account.current)) :
    (Future.owner input depth count base initial support owner run account tail).1 =
      liftResponsibility input depth count base initial run owner.1 := by
  induction run with
  | nil => rfl
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact congrArg Sum.inl (inherited (Future.prependEdge input depth count (.admit claim) rfl tail))
      | cross slot obligation present boundary =>
          exact inherited (Future.prependEdge input depth count (.cross slot obligation present boundary) rfl tail)
      | reopen _ _ _ impossible => exact impossible.elim

#print axioms actual_frame_owner_key
#print axioms owner_key_is_the_original_lift

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Keys
