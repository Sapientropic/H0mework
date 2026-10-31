import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

theorem active_finite {world : WorldRelationNetwork} {law : DebtActivationLaw}
    {support : world.Support} (state : law.DebtState)
    (prior : Finite (OpenResponsibilityAt world support)) :
    Finite (OpenResponsibilityAt (ExtendedNetwork world law) (support, some state)) := by
  let := prior
  let presentation := activeInventoryPresentation (law := law) state
    (ConstructivePresentation.refl (OpenResponsibilityAt world support))
  exact Finite.of_surjective presentation.forward
    (fun entry => ⟨presentation.backward entry, presentation.forward_backward entry⟩)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem old_fold_finite {world : WorldRelationNetwork} (support : world.Support)
    (baseFinite : Finite (OpenResponsibilityAt world support)) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (target : (Epoch.Finance.process input depth count).GeneratedState) →
    (tail : Nonempty ((Epoch.Finance.process input depth count).Run
      (Epoch.Finance.Legacy.generated input depth count (Epoch.Finance.World.OldAccount input run)).current target.current)) →
    Finite (OpenResponsibilityAt (Epoch.Finance.World.folded input depth count world run)
      (Epoch.Finance.World.currentSupport input depth count world support run target tail)) := by
  intro current run
  induction run with
  | nil => intro target tail; exact baseFinite
  | step prior edge inherited =>
      intro target tail
      cases edge with
      | admit claim => exact active_finite _ (inherited target _)
      | cross _ _ _ _ => exact inherited target _
      | reopen _ _ _ impossible => exact impossible.elim

theorem shape_support_finite {native : Financial.Installation.NativeFrame input}
    (shape : Epoch.Finance.Installation.Shape input native) (current : native.V.Current)
    (target : (Epoch.Finance.process input depth count).GeneratedState)
    (tail : Nonempty ((Epoch.Finance.process input depth count).Run
      (Epoch.Finance.Legacy.generated input depth count (native.cursor current).account).current target.current)) :
    Finite (OpenResponsibilityAt (shape.world input depth count)
      (shape.support input depth count current target tail)) := by
  induction shape with
  | base start positive =>
      exact old_fold_finite input depth count _
        (Financial.Installation.base_finite input (Financial.Installation.Cursor.physicalVisit input current.cursor).current) _ target _
  | born prior registered inherited =>
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact active_finite _ (inherited _ tail)
      | registered native => exact active_finite _ (inherited _ tail)

theorem future_support_finite {world : WorldRelationNetwork}
    (initial : (Epoch.Finance.process input depth count).GeneratedState)
    (support : world.Support) (baseFinite : Finite (OpenResponsibilityAt world support)) :
    {current : ResponsibilityState (Epoch.Finance.vocabulary input depth count)} →
    (run : (Epoch.Finance.process input depth count).Run initial.current current) →
    (target : (Epoch.Finance.process input depth count).GeneratedState) →
    (tail : Nonempty ((Epoch.Finance.process input depth count).Run current target.current)) →
    Finite (OpenResponsibilityAt (Epoch.Finance.Future.world input depth count world initial run)
      (Epoch.Finance.Future.support input depth count world initial support run target tail)) := by
  intro current run
  induction run with
  | nil => intro target tail; exact baseFinite
  | step prior edge inherited =>
      intro target tail
      cases edge with
      | admit claim => exact active_finite _ (inherited target _)
      | cross _ _ _ _ => exact inherited target _
      | reopen _ _ _ impossible => exact impossible.elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness
