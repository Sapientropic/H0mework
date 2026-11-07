import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem target_emitted {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    (emit : (state : V.Current) → source.toRootSource.actual.OccurrenceAt state)
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    (commutes : generated.CommutesWith emit) :
    successor.targetOccurrence = emit successor.targetCurrent := by
  cases generated <;> first | exact commutes | exact successor.elim

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

namespace NativeFrame

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition}

def sourceSupport (current : frame.V.Current) :=
  frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (frame.root.emitted current)

def next (current : frame.V.Current) := (frame.successor current).targetCurrent

theorem target_occurrence (current : frame.V.Current) :
    (frame.successor current).targetOccurrence = frame.root.emitted (frame.next current) :=
  target_emitted frame.root.emitted _ _ (frame.root.compiler_commutes current)

def wholeEvolution (current : frame.V.Current) :
    LedgerWriteEvolutionAt frame.N ⟨frame.sourceSupport current⟩ ⟨frame.sourceSupport (frame.next current)⟩ :=
  Eq.mp (congrArg (fun occurrence => LedgerWriteEvolutionAt frame.N ⟨frame.sourceSupport current⟩
    ⟨frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence⟩)
      (frame.target_occurrence current)) (frame.successor current).ledgerEvolution

private theorem cast_keys {world : WorldRelationNetwork} {source before after : world.Support}
    (same : before = after) (evolution : LedgerWriteEvolutionAt world ⟨source⟩ ⟨before⟩)
    (kept : Financial.Installation.KeepsKeys evolution) :
    Financial.Installation.KeepsKeys
      (Eq.mp (congrArg (fun target => LedgerWriteEvolutionAt world ⟨source⟩ ⟨target⟩) same) evolution) := by
  cases same
  exact kept

theorem whole_keys (current : frame.V.Current) : Financial.Installation.KeepsKeys (frame.wholeEvolution current) := by
  exact cast_keys (congrArg frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (frame.target_occurrence current)) (frame.successor current).ledgerEvolution (frame.successor_keys current)

def account (current : frame.V.Current) := (frame.cursor current).account

def item? (current : frame.V.Current) :=
  Accounting.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (frame.cursor current)

theorem account_next_of_item (current : frame.V.Current) (item : Epoch.Finance.ActualItem input depth count)
    (found : frame.item? current = some item) :
    frame.account (frame.next current) = (Epoch.Finance.consume input depth count item (frame.account current)).next input depth count := by
  have nextCursor := congrArg Accounting.Current.account (frame.next_exact current)
  exact nextCursor.trans (Accounting.account_next_of_item (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (frame.cursor current) item found)

theorem account_next_of_empty (current : frame.V.Current) (absent : frame.item? current = none) :
    frame.account (frame.next current) = frame.account current := by
  have nextCursor := congrArg Accounting.Current.account (frame.next_exact current)
  exact nextCursor.trans (Accounting.account_next_of_empty (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (frame.cursor current) absent)

def native (current : frame.V.Current) : (Epoch.Finance.process input depth count).Run
    (frame.account current).current (frame.account (frame.next current)).current := by
  have source := Accounting.nativeTransition (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (frame.cursor current)
  have same := congrArg (fun cursor => cursor.account.current) (frame.next_exact current)
  exact same.symm ▸ source

end NativeFrame

structure HeadRegistration (current : frame.V.Current) where
  private mk ::
  item : Epoch.Finance.ActualItem input depth count
  atHead : frame.item? current = some item
  issued : Registration input depth count item (frame.account current)

def headRegistration? (current : frame.V.Current) :
    Option (HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current) :=
  match selected : frame.item? current with
  | none => none
  | some item => (registration? input depth count item (frame.account current)).map (fun issued => ⟨item, selected, issued⟩)

namespace HeadRegistration

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame}

variable {current : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current)

def law := registered.issued.law input depth count

def firstStep := registered.issued.firstStep input depth count

def admitted := registered.issued.admitted input depth count

theorem actual_next_account : frame.account (frame.next current) = registered.admitted := by
  rw [frame.account_next_of_item current registered.item registered.atHead]
  rw [registered.issued.selected]
  rfl

end HeadRegistration

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro
