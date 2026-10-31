import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation (KeepsKeys wholeTransport_keeps_keys)

noncomputable section

theorem extended_subsingleton {base : WorldRelationNetwork} (law : DebtActivationLaw)
    (fibres : ∀ support responsibility, Subsingleton (base.OpenAt support responsibility))
    (support : (ExtendedNetwork base law).Support) (responsibility : (ExtendedNetwork base law).Responsibility) :
    Subsingleton ((ExtendedNetwork base law).OpenAt support responsibility) := by
  rcases support with ⟨support, active⟩
  cases responsibility with
  | inl old => exact fibres support old
  | inr debt => cases active <;> dsimp only [ExtendedNetwork, extendedNetwork, DebtOpenAt] <;> infer_instance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem old_fibres : {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    ∀ support responsibility, Subsingleton ((Epoch.Finance.World.folded input depth count (ProgrammeSource.N input) run).OpenAt support responsibility) := by
  intro current run
  induction run with
  | nil =>
      intro support responsibility
      change Subsingleton (ProgrammeWorld.OpenAt support responsibility)
      cases support <;> cases responsibility <;> dsimp only [ProgrammeWorld.OpenAt] <;> infer_instance
  | step prior edge inherited =>
      cases edge with
      | admit _ => exact extended_subsingleton _ inherited
      | cross _ _ _ _ => exact inherited
      | reopen _ _ _ impossible => exact impossible.elim

theorem shape_fibres {native : Financial.Installation.NativeFrame input}
    (shape : Epoch.Finance.Installation.Shape input native) :
    ∀ support responsibility, Subsingleton ((shape.world input depth count).OpenAt support responsibility) := by
  induction shape with
  | base start _ => exact old_fibres input depth count start.account.generated
  | born _ _ inherited => exact extended_subsingleton _ inherited

theorem future_fibres {base : WorldRelationNetwork}
    (initial : (Epoch.Finance.process input depth count).GeneratedState)
    (fibres : ∀ support responsibility, Subsingleton (base.OpenAt support responsibility)) :
    {current : ResponsibilityState (Epoch.Finance.vocabulary input depth count)} →
    (run : (Epoch.Finance.process input depth count).Run initial.current current) →
    ∀ support responsibility, Subsingleton ((Epoch.Finance.Future.world input depth count base initial run).OpenAt support responsibility) := by
  intro current run
  induction run with
  | nil => exact fibres
  | step prior edge inherited =>
      cases edge with
      | admit _ => exact extended_subsingleton _ inherited
      | cross _ _ _ _ => exact inherited
      | reopen _ _ _ impossible => exact impossible.elim

theorem old_evolution_keys (base : WorldRelationNetwork) {before after : base.Support}
    (baseEvolution : LedgerWriteEvolutionAt base ⟨before⟩ ⟨after⟩)
    (baseOwner : OpenResponsibilityAt base before) (same : KeepsKeys baseEvolution) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (account : (Epoch.Finance.process input depth count).GeneratedState) →
    (tail : Nonempty ((Epoch.Finance.process input depth count).Run
      (Epoch.Finance.Legacy.generated input depth count (Epoch.Finance.World.OldAccount input run)).current account.current)) →
    (item : Epoch.Finance.ActualItem input depth count) →
    KeepsKeys (Epoch.Finance.World.continueItemEvolution input depth count base baseEvolution baseOwner run account tail item) := by
  intro current run
  induction run with
  | nil => intro account tail item; exact same
  | step prior edge inherited =>
      intro account tail item
      cases edge with
      | admit _ => exact wholeTransport_keeps_keys _ _ _ (inherited account _ item)
      | cross _ _ _ _ => exact inherited account _ item
      | reopen _ _ _ impossible => exact impossible.elim

theorem shape_evolution_keys {native : Financial.Installation.NativeFrame input}
    (shape : Epoch.Finance.Installation.Shape input native) (current : native.V.Current)
    (ready : shape.Ready input current) (account : (Epoch.Finance.process input depth count).GeneratedState)
    (tail : Nonempty ((Epoch.Finance.process input depth count).Run
      (Epoch.Finance.Legacy.generated input depth count (native.cursor current).account).current account.current))
    (item : Epoch.Finance.ActualItem input depth count) :
    KeepsKeys (shape.continueItemEvolution input depth count current ready account tail item) := by
  induction shape with
  | base start positive => exact old_evolution_keys input depth count _ _ _ ⟨fun _ => rfl, fun _ => rfl⟩ _ account _ item
  | born prior registered inherited =>
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native =>
          exact wholeTransport_keeps_keys _
            (prior.currentOwner input depth count current account tail) _ (inherited _ ready.1 tail)

theorem future_evolution_keys {base : WorldRelationNetwork}
    (initial : (Epoch.Finance.process input depth count).GeneratedState)
    {before after : base.Support} (baseEvolution : LedgerWriteEvolutionAt base ⟨before⟩ ⟨after⟩)
    (baseOwner : OpenResponsibilityAt base before) (same : KeepsKeys baseEvolution) :
    {current : ResponsibilityState (Epoch.Finance.vocabulary input depth count)} →
    (run : (Epoch.Finance.process input depth count).Run initial.current current) →
    (account : (Epoch.Finance.process input depth count).GeneratedState) →
    (tail : Nonempty ((Epoch.Finance.process input depth count).Run current account.current)) →
    (item : Epoch.Finance.ActualItem input depth count) →
    KeepsKeys (Epoch.Finance.Future.itemEvolution input depth count base initial baseEvolution baseOwner run account tail item) := by
  intro current run
  induction run with
  | nil => intro account tail item; exact same
  | step prior edge inherited =>
      intro account tail item
      cases edge with
      | admit _ => exact wholeTransport_keeps_keys _ _ _ (inherited account _ item)
      | cross _ _ _ _ => exact inherited account _ item
      | reopen _ _ _ impossible => exact impossible.elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure
