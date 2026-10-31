import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.First

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

/-- Canonical authority follows the actual compiler destination, including
its dependent target support; it does not choose another row after the event. -/
theorem canonical_destination_heq {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure N V) (current next : V.Current)
    (nextEq : (root.toRoot.evolutionAt current).nextCurrent? = some next)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted current) (root.generatedLedgerAt current))
    (entry : OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted current))) :
    HEq (root.canonicalTargetEntryAtNext nextEq entry) (successor.ledgerEvolution.destination entry).1 := by
  revert successor
  unfold SourceNativeLedgerRootClosure.canonicalTargetEntryAtNext
  dsimp only [SourceNativeLedgerRootClosure.generatedLedgerAt] at *
  generalize_proofs at *
  generalize imageEq : root.source.ledgerCompiler.compile (root.emitted current) = image at *
  cases image with
  | nativeWrite write structural target evolution =>
      intro successor
      have targetEq : V.nativeTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
        rw [structural] at nextEq
        exact Option.some.inj nextEq
      cases targetEq
      have commutes := root.compiler_commutes current
      rw [imageEq] at commutes
      cases commutes
      rfl
  | relationWrite write structural target evolution =>
      intro successor
      have targetEq : V.relationTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
        rw [structural] at nextEq
        exact Option.some.inj nextEq
      cases targetEq
      have commutes := root.compiler_commutes current
      rw [imageEq] at commutes
      cases commutes
      rfl
  | continuedTransport write structural target evolution =>
      intro successor
      have targetEq : V.continuedTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
        rw [structural] at nextEq
        exact Option.some.inj nextEq
      cases targetEq
      have commutes := root.compiler_commutes current
      rw [imageEq] at commutes
      cases commutes
      rfl
  | borromeanRedirect write structural target evolution =>
      intro successor
      have targetEq : V.redirectTarget write = next := by
        change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
        rw [structural] at nextEq
        exact Option.some.inj nextEq
      cases targetEq
      have commutes := root.compiler_commutes current
      rw [imageEq] at commutes
      cases commutes
      rfl
  | faithfulTerminal => intro successor; exact successor.elim

#print axioms canonical_destination_heq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
