import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.Body
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def sameSupportLedger {N : WorldRelationNetwork} {before after : N.Support}
    (same : after = before) : ConstructiveRetract (OpenResponsibilityAt N before) (OpenResponsibilityAt N after) := by
  cases same
  exact ⟨id, id, fun _ => rfl⟩

private theorem sameSupportLedger_heq {N : WorldRelationNetwork} {before after : N.Support}
    (same : after = before) : HEq (sameSupportLedger same)
      ((Financial.Installation.Ingress.identityTranslation N).oldOpenLedger before) := by
  cases same
  exact HEq.rfl

private theorem sameSupportLedger_rows {N : WorldRelationNetwork} {before after : N.Support}
    (same : after = before) :
    (∀ entry, ((sameSupportLedger same).forward entry).1 = entry.1) ∧
    (∀ entry, ((sameSupportLedger same).forward entry).claim = entry.claim) ∧
    (∀ entry, ((sameSupportLedger same).forward entry).progressBudget = entry.progressBudget) ∧
    (∀ entry, (sameSupportLedger same).forward ((sameSupportLedger same).backward entry) = entry) := by
  cases same
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (data : Continuation.FinancialData frame) (reader : Reader input depth count)
  {current : frame.V.Current} (germ : GermAt frame data reader current)

abbrev translation := Financial.Installation.Ingress.identityTranslation frame.N

def initialLedger : ConstructiveRetract
    (OpenResponsibilityAt frame.N (frame.sourceSupport current))
    (OpenResponsibilityAt frame.N ((bareFrame frame data reader germ).sourceSupport (bodyInitial frame data reader germ))) :=
  sameSupportLedger (initial_support_is_the_original_current frame data reader germ)

theorem initial_ledger_is_the_original_identity : HEq (initialLedger frame data reader germ)
    ((translation frame).oldOpenLedger (frame.sourceSupport current)) :=
  sameSupportLedger_heq (initial_support_is_the_original_current frame data reader germ)

theorem initial_ledger_preserves_responsibility
    (entry : OpenResponsibilityAt frame.N (frame.sourceSupport current)) :
    ((initialLedger frame data reader germ).forward entry).1 = entry.1 :=
  (sameSupportLedger_rows (initial_support_is_the_original_current frame data reader germ)).1 entry

theorem initial_ledger_preserves_claim
    (entry : OpenResponsibilityAt frame.N (frame.sourceSupport current)) :
    ((initialLedger frame data reader germ).forward entry).claim = entry.claim :=
  (sameSupportLedger_rows (initial_support_is_the_original_current frame data reader germ)).2.1 entry

theorem initial_ledger_preserves_budget
    (entry : OpenResponsibilityAt frame.N (frame.sourceSupport current)) :
    ((initialLedger frame data reader germ).forward entry).progressBudget = entry.progressBudget :=
  (sameSupportLedger_rows (initial_support_is_the_original_current frame data reader germ)).2.2.1 entry

theorem initial_ledger_has_no_fresh_row
    (entry : OpenResponsibilityAt frame.N ((bareFrame frame data reader germ).sourceSupport (bodyInitial frame data reader germ))) :
    (initialLedger frame data reader germ).forward ((initialLedger frame data reader germ).backward entry) = entry :=
  (sameSupportLedger_rows (initial_support_is_the_original_current frame data reader germ)).2.2.2 entry

def initialRow (entry : OpenResponsibilityAt frame.N (frame.sourceSupport current)) :
    ((bareFrame frame data reader germ).root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (bareFrame frame data reader germ).root.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
      ((initialLedger frame data reader germ).forward entry) := by
  let compiler := Reentry.ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ)
  let occurrence := Reentry.emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ) (bodyInitial frame data reader germ)
  let translated := (initialLedger frame data reader germ).forward entry
  let selected := sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
    compiler.writeRowSource compiler.terminalRowSource (compiler.compile occurrence) (compiler.compilePatch occurrence) translated
  have present : selected.isSome = true := by
    let check (packet : Σ image : SourceNativeLedgerEvolutionAt _ occurrence,
        SourceNativeFiniteLedgerPatchAt _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource image) : Bool :=
      (sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
        compiler.writeRowSource compiler.terminalRowSource packet.1 packet.2 translated).isSome
    change check (Reentry.sourcePacket (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ) occurrence) = true
    dsimp only [occurrence, Reentry.sourcePacket]
    split <;> rfl
  exact SourceNativeTemporalVisitGeneratedEvolutionAt.GeneratedEntryRowAt.ofSourceRow (selected.get present)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.initial_ledger_is_the_original_identity
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.initialRow
