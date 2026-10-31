import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation Quantifiers.Joint
open Financial.Installation (KeepsKeys wholeTransport_keeps_keys)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

private theorem original_keys (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    {A B : WorldRelationNetwork} (map : TypedSemanticWorldNetworkTranslationAt A B)
    (before : A.Support) (after : B.Support)
    (base : LedgerWriteEvolutionAt B ⟨map.support.forward before⟩ ⟨after⟩)
    (owner : OpenResponsibilityAt A before) (same : KeepsKeys base)
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current)
    (account : (Financial.process input).GeneratedState)
    (tail : Nonempty ((Financial.process input).Run current account.current)) :
    KeepsKeys (Abolition.Root.Epoch.Finance.World.enterEvolution input depth count map before after base owner run account tail) := by
  induction run with
  | nil => exact same
  | step prior edge ih => cases edge with
      | admit _ => exact wholeTransport_keeps_keys _ _ _ (ih _)
      | cross slot obligation present boundary => exact ih _
      | reopen _ _ _ impossible => exact impossible.elim

private theorem shape_keys (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    {native : Financial.Installation.NativeFrame input} (shape : Abolition.Root.Epoch.Finance.Installation.Shape input native)
    (current : native.V.Current) (ready : shape.Ready input current) :
    KeepsKeys (shape.enterEvolution input depth count current ready) := by
  induction shape with
  | base start positive => exact original_keys input depth count _ _ _ _ _ ⟨fun _ => rfl,fun _ => rfl⟩ _ _ _
  | @born old prior origin registered ih =>
      rcases current with ⟨current,event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native =>
          exact wholeTransport_keeps_keys _
            (((prior.translation input depth count).oldOpenLedger _).forward (old.entrySupport _))
            _ (ih current ready.1)

variable {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

theorem the_actual_background_representation_keeps_all_original_keys : KeepsKeys (Background.enterEvolution seed) :=
  shape_keys seed.input seed.depth seed.count (Background.shape seed) (Background.visit seed).current
    (Background.all_existing_native_rows_are_registered_at_this_actual_visit seed)

theorem the_joint_entered_evolution_keeps_all_original_keys : KeepsKeys (enteredEvolution seed grossClaim) :=
  wholeTransport_keeps_keys (Background.enterEvolution seed) (baseOwner seed) (Productive.enter seed grossClaim)
    (the_actual_background_representation_keeps_all_original_keys seed)

private theorem source_cast_keys {N : WorldRelationNetwork} {left right target : N.Support}
    (same : left = right) (movement : LedgerWriteEvolutionAt N ⟨right⟩ ⟨target⟩)
    (keys : KeepsKeys movement) : KeepsKeys (same.symm ▸ movement) := by cases same; exact keys

theorem every_original_key_is_retained_by_the_same_joint_write : KeepsKeys (evolution seed grossClaim) :=
  source_cast_keys (mapped_support_is_the_same_actual_background_and_original_productive_row seed grossClaim)
    (enteredEvolution seed grossClaim) (the_joint_entered_evolution_keeps_all_original_keys seed grossClaim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
