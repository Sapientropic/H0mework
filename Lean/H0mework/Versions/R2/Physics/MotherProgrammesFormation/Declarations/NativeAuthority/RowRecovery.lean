import H0mework.Versions.R2.Foundation.Cofinal.TemporalAnswer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace MotherNativeAuthority

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {source : SourceNativeSource N V}
variable {ExactTransitionAt :
  {current : V.Current} → (occurrence : source.toRootSource.actual.OccurrenceAt current) →
    {targetSupport : N.Support} →
    OpenResponsibilityAt N (source.toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt N targetSupport → Type u}
variable {writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
variable {terminalRowSource : LedgerTerminalRowSourceAt source}
variable {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}

private theorem write_selector_recovers {target : CompleteLiveLedgerAt N}
    (patch : FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence target)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf occurrence))
    (row : patch.CanonicalGeneratedSourceRowAt entry) :
    patch.canonicalGeneratedSourceRow? entry = some row := by
  cases patch with
  | identityRemainder rows coverage =>
      rcases row with ⟨indexed, selected⟩
      simp only [FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow?]
      split
      · rename_i absent
        cases selected.symm.trans absent
      · rename_i other queried
        have same : other = indexed := Option.some.inj (queried.symm.trans selected)
        cases same
        rfl
  | complete rows coverage => rcases row with ⟨⟩; rfl
  | transportedRemainder rows coverage remainder =>
      cases row with
      | inl exceptional =>
          rcases exceptional with ⟨indexed, selected⟩
          simp only [FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow?]
          split
          · rename_i absent
            cases selected.symm.trans absent
          · rename_i other queried
            have same : other = indexed := Option.some.inj (queried.symm.trans selected)
            cases same
            rfl
      | inr transported =>
          rcases transported with ⟨omitted⟩
          simp only [FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow?]
          split
          · rfl
          · rename_i other queried
            cases omitted.symm.trans queried

private theorem terminal_selector_recovers
    (patch : SourceGeneratedLedgerTerminalPatchAt terminalRowSource occurrence)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf occurrence))
    (row : patch.CanonicalGeneratedEntryAt entry) :
    patch.canonicalGeneratedEntryAt entry = row := by
  cases patch with
  | finite finite => rcases row with ⟨⟩; rfl
  | supportSettlement generated => rcases row with ⟨⟩; rfl

private theorem branch_selector_recovers
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (patch : SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
      writeRowSource terminalRowSource generated)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf occurrence))
    (row : SourceNativeFiniteLedgerPatchGeneratedEntryAt source ExactTransitionAt
      writeRowSource terminalRowSource generated patch entry) :
    sourceNativeFiniteLedgerPatchGeneratedEntry? source ExactTransitionAt
      writeRowSource terminalRowSource generated patch entry = some row := by
  cases generated with
  | nativeWrite => exact write_selector_recovers patch.1 entry row
  | relationWrite => exact write_selector_recovers patch.1 entry row
  | continuedTransport => exact write_selector_recovers patch.1 entry row
  | borromeanRedirect => exact write_selector_recovers patch.1 entry row
  | faithfulTerminal => exact congrArg some (terminal_selector_recovers patch.1 entry row)

/-- The original temporal selector recovers the full original row token in every patch branch. -/
theorem row_selector_recovers
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (generated : SourceNativeTemporalVisitGeneratedEvolutionAt root visit)
    (entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf (root.emitted visit.current)))
    (row : generated.GeneratedEntryRowAt entry) :
    generated.canonicalGeneratedEntryRow? entry = some row := by
  rcases row with ⟨sourceRow⟩
  have recovered := branch_selector_recovers
    (root.generatedLedgerAt visit.current) generated.currentPatch entry sourceRow
  simp only [SourceNativeTemporalVisitGeneratedEvolutionAt.canonicalGeneratedEntryRow?, recovered]

end MotherNativeAuthority
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
