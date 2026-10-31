import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.InventoryFold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

/-- The source supplies raw syntax at the current physical/financial read.
It supplies no checked command, target account, or successful continuation. -/
abbrev Reader := Physical.Cursor Party Good Port Technology Instrument →
  (Epoch.Finance.process input depth count).GeneratedState →
  Compile.RawInput Party Good Port Technology Instrument

variable {input depth count}
  {prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (data : Continuation.FinancialData frame) (reader : Reader input depth count)

def Available (current : frame.V.Current) : Prop :=
  data.Ready current ∧
    Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor current) ∧
    Bound.Complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor current)

/-- The literal consumed past is retained even when the raw reader and all
material readouts are constant. Distinct input occurrences stay distinguishable. -/
structure GermAt (current : frame.V.Current) where
  private mk ::
  snapshot : Physical.Cursor Party Good Port Technology Instrument
  account : (Epoch.Finance.process input depth count).GeneratedState
  raw : Compile.RawInput Party Good Port Technology Instrument
  private snapshot_eq : snapshot = Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal
  private account_eq : account = frame.account current
  private raw_eq : raw = reader snapshot account
  ready : data.Ready current
  sourceFold : Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    start proposal sourcePosition (frame.cursor current)
  complete : Bound.Complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    start proposal sourcePosition (frame.cursor current)

def germAt (current : frame.V.Current) (available : Available frame data current) :
    GermAt frame data reader current :=
  ⟨Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal, frame.account current,
    reader (Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal) (frame.account current),
    rfl, rfl, rfl, available.1, available.2.1, available.2.2⟩

theorem germ_unique (current : frame.V.Current) (available : Available frame data current)
    (germ : GermAt frame data reader current) : germ = germAt frame data reader current available := by
  rcases germ with ⟨snapshot, account, raw, snapshot_eq, account_eq, raw_eq, ready, sourceFold, complete⟩
  subst snapshot
  subst account
  subst raw
  rfl

def ResultAt {current : frame.V.Current} (germ : GermAt frame data reader current) :=
  Mandatory.Report (review := review) input depth count prefixLimit renewalLimit germ.snapshot germ.raw ×
    Compile.Result input depth count prefixLimit renewalLimit
      (Physical.stateAt input depth count prefixLimit renewalLimit germ.snapshot.past)
      (Mandatory.executionRaw (review := review) input depth count prefixLimit renewalLimit germ.snapshot germ.raw)

def reportAt {current : frame.V.Current} (germ : GermAt frame data reader current) : ResultAt frame data reader germ :=
  ⟨Mandatory.produce (review := review) input depth count prefixLimit renewalLimit germ.snapshot germ.raw,
    Physical.resultAt input depth count prefixLimit renewalLimit
      (Mandatory.executionCursor (review := review) input depth count prefixLimit renewalLimit germ.snapshot germ.raw)⟩

theorem input_uses_the_literal_current_account {current : frame.V.Current}
    (germ : GermAt frame data reader current) :
    germ.account = frame.account current ∧
      germ.snapshot = Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal ∧
      germ.raw = reader germ.snapshot germ.account :=
  ⟨germ.account_eq, germ.snapshot_eq, germ.raw_eq⟩

theorem next_seed_is_generated_by_the_original_history {current : frame.V.Current}
    (germ : GermAt frame data reader current) :
    Accounting.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount germ.snapshot germ.raw 0 =
      frame.account current := by
  change Inventory.before input depth count prefixLimit renewalLimit sourceDepth sourceCount germ.snapshot = _
  rw [germ.snapshot_eq]
  exact (Continuation.completed_root_account_is_the_literal_next_input_seed (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition (frame.cursor current) germ.sourceFold germ.complete).symm

#print axioms germ_unique
#print axioms reportAt
#print axioms next_seed_is_generated_by_the_original_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw
