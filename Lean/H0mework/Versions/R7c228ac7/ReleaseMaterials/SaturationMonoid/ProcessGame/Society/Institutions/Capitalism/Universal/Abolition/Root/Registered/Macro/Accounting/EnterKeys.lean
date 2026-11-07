import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Enter
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation (KeepsKeys wholeTransport_keeps_keys)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

private theorem old_enter_keys {OldBase NewBase : WorldRelationNetwork}
    (baseMap : TypedSemanticWorldNetworkTranslationAt OldBase NewBase)
    (before : OldBase.Support) (after : NewBase.Support)
    (evolution : LedgerWriteEvolutionAt NewBase ⟨baseMap.support.forward before⟩ ⟨after⟩)
    (owner : OpenResponsibilityAt OldBase before) (kept : KeepsKeys evolution) :
    {current : ResponsibilityState (Financial.vocabulary input)} →
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) →
    (account : (Financial.process input).GeneratedState) →
    (tail : Nonempty ((Financial.process input).Run current account.current)) →
    KeepsKeys (Epoch.Finance.World.enterEvolution input depth count baseMap before after evolution owner run account tail) := by
  intro current run
  induction run with
  | nil => intro account tail; exact kept
  | step prior edge inherited =>
      intro account tail
      cases edge with
      | admit _ => exact wholeTransport_keeps_keys _ _ _ (inherited account _)
      | cross _ _ _ _ => exact inherited account _
      | reopen _ _ _ impossible => exact impossible.elim

private theorem shape_enter_keys {native : Financial.Installation.NativeFrame input}
    (shape : Epoch.Finance.Installation.Shape input native) (current : native.V.Current)
    (ready : shape.Ready input current) :
    KeepsKeys (shape.enterEvolution input depth count current ready) := by
  induction shape with
  | base start positive => exact old_enter_keys input depth count _ _ _ _ _ ⟨fun _ => rfl, fun _ => rfl⟩ _ _ _
  | @born old prior origin registered inherited =>
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native =>
          exact wholeTransport_keeps_keys _
            ((prior.translation input depth count).oldOpenLedger _ |>.forward (old.entrySupport _))
            _ (inherited current ready.1)

theorem generated_entry_keeps_every_original_key (sourceDepth sourceCount : Nat) :
    KeepsKeys (Epoch.Finance.Installation.Generated.enterEvolution input depth count sourceDepth sourceCount) :=
  shape_enter_keys input depth count _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
