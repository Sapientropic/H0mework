import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Frame
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Foundation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def ImageKeepsKeys {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  match image with
  | .nativeWrite _ _ _ evolution | .relationWrite _ _ _ evolution
  | .continuedTransport _ _ _ evolution | .borromeanRedirect _ _ _ evolution =>
      Financial.Installation.KeepsKeys evolution
  | .faithfulTerminal .. => True

private theorem image_keys_of_actual {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {image : SourceNativeLedgerEvolutionAt source occurrence}
    (actual : SourceNativeLedgerGeneratedSuccessorAt occurrence image)
    (same : Financial.Installation.KeepsKeys actual.ledgerEvolution) : ImageKeepsKeys image := by
  cases image <;> first | exact same | trivial

private def entryFromImage {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure N V) {current next : V.Current}
    (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next)
    (sourceEntry : OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted current)))
    (image : SourceNativeLedgerEvolutionAt root.source.source (root.emitted current))
    (image_eq : root.generatedLedgerAt current = image) :
    OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted next)) := by
  cases generated_eq : image with
  | nativeWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.nativeTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.nativeTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .nativeWrite write structural_eq targetOccurrence ledgerEvolution from
            image_eq.trans generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | relationWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.relationTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.relationTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .relationWrite write structural_eq targetOccurrence ledgerEvolution from
            image_eq.trans generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | continuedTransport write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.continuedTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.continuedTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .continuedTransport write structural_eq targetOccurrence ledgerEvolution from
            image_eq.trans generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | borromeanRedirect write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.redirectTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.redirectTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .borromeanRedirect write structural_eq targetOccurrence ledgerEvolution from
            image_eq.trans generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | faithfulTerminal terminal structural_eq ledgerEvolution =>
      change
        (root.source.source.toRootSource.actual.compile
          (root.emitted current)).nextCurrent? = some next at next_eq
      rw [structural_eq] at next_eq
      contradiction

private theorem entryFromImage_keeps_key {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure N V) {current next : V.Current}
    (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next)
    (entry : OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted current)))
    (image : SourceNativeLedgerEvolutionAt root.source.source (root.emitted current))
    (image_eq : root.generatedLedgerAt current = image)
    (same : ImageKeepsKeys image) : (entryFromImage root next_eq entry image image_eq).1 = entry.1 := by
  cases image with
  | nativeWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.nativeTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq : targetOccurrence = root.emitted (V.nativeTarget write) := by
        have commutes := root.compiler_commutes current
        change (root.generatedLedgerAt current).CommutesWith root.emitted at commutes
        rw [image_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      change ((ledgerEvolution.destination entry).1).1 = entry.1
      exact same.1 entry
  | relationWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.relationTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq : targetOccurrence = root.emitted (V.relationTarget write) := by
        have commutes := root.compiler_commutes current
        change (root.generatedLedgerAt current).CommutesWith root.emitted at commutes
        rw [image_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      change ((ledgerEvolution.destination entry).1).1 = entry.1
      exact same.1 entry
  | continuedTransport write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.continuedTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq : targetOccurrence = root.emitted (V.continuedTarget write) := by
        have commutes := root.compiler_commutes current
        change (root.generatedLedgerAt current).CommutesWith root.emitted at commutes
        rw [image_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      change ((ledgerEvolution.destination entry).1).1 = entry.1
      exact same.1 entry
  | borromeanRedirect write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.redirectTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq : targetOccurrence = root.emitted (V.redirectTarget write) := by
        have commutes := root.compiler_commutes current
        change (root.generatedLedgerAt current).CommutesWith root.emitted at commutes
        rw [image_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      change ((ledgerEvolution.destination entry).1).1 = entry.1
      exact same.1 entry
  | faithfulTerminal terminal structural_eq ledgerEvolution =>
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at next_eq
      rw [structural_eq] at next_eq
      contradiction

private theorem canonical_entry_keeps_key {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure N V) {current next : V.Current}
    (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next)
    (entry : OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted current)))
    (same : ImageKeepsKeys (root.generatedLedgerAt current)) :
    (root.canonicalTargetEntryAtNext next_eq entry).1 = entry.1 := by
  exact entryFromImage_keeps_key root next_eq entry (root.generatedLedgerAt current) rfl same

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

theorem canonical_successor_keeps_the_original_entry (basis : Inquiry.Basis frame.N)
    (stable : ∀ left right, (basis.entry left).1 = (basis.entry right).1)
    (current : frame.V.Current) :
    frame.root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
      (frame.successor current).next_eq (basis.entry (frame.sourceSupport current)) =
        basis.entry (frame.sourceSupport (frame.next current)) := by
  apply Financial.Installation.entry_eq_of_key
  · exact (canonical_entry_keeps_key _ _ _
      (image_keys_of_actual (frame.successor current) (frame.successor_keys current))).trans (stable _ _)
  · exact frame.open_fibres _

#print axioms canonical_successor_keeps_the_original_entry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation
