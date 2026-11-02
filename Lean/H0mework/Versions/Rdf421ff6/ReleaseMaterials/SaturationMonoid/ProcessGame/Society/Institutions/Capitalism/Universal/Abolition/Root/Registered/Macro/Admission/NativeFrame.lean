import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Living

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def ImageKeepsKeys {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt occurrence image,
    Financial.Installation.KeepsKeys actual.ledgerEvolution

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

def successor (current : Current frame registered) : SourceNativeLedgerGeneratedSuccessorAt
    (emitted frame registered current) ((livingRoot frame registered).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) := by
  change SourceNativeLedgerGeneratedSuccessorAt (emitted frame registered current)
    ((ledgerCompiler frame registered).compile (emitted frame registered current))
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> exact PUnit.unit

theorem successor_current (current : Current frame registered) :
    (successor frame registered current).targetCurrent = next frame registered current := by
  have actual : ((source frame registered).toRootSource.actual.compile (emitted frame registered current)).nextCurrent? =
      some (next frame registered current) := by
    rw [source_choice]
    split <;> rfl
  exact Option.some.inj ((successor frame registered current).next_eq.symm.trans actual)

theorem successor_keys (current : Current frame registered) :
    Financial.Installation.KeepsKeys (successor frame registered current).ledgerEvolution := by
  have paidRows : Financial.Installation.KeepsKeys (patch frame registered current).toLedgerWriteEvolution := by
    unfold Financial.Installation.KeepsKeys
    rw [patch_destination, patch_origin]
    exact whole_keys frame registered current
  have all : ImageKeepsKeys ((ledgerCompiler frame registered).compile (emitted frame registered current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact paidRows
  exact all _

def nativeFrame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition where
  nativeOrigin := frame.nativeOrigin
  N := N frame registered
  V := V frame registered
  root := livingRoot frame registered
  cursor := fun current => frame.cursor current.1
  successor := successor frame registered
  next_exact := by
    intro current
    exact (congrArg (fun target : Current frame registered => frame.cursor target.1)
      (successor_current frame registered current)).trans (frame.next_exact current.1)
  entry := fun current => oldEntry (state? := some (state frame registered current.2)) (frame.entry current.1)
  entries_finite := entry_finite frame registered
  open_fibres := open_fibres frame registered
  successor_keys := successor_keys frame registered

theorem first_source_step_registers_the_same_original_debt :
    (nativeFrame frame registered).account
        (successor frame registered (initial frame registered)).targetCurrent = registered.admitted := by
  exact (congrArg (fun target : Current frame registered => frame.account target.1)
    (successor_current frame registered (initial frame registered))).trans registered.actual_next_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
