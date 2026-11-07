import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Continuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem canonical_key {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure N V) (current next : V.Current)
    (nextEq : (root.toRoot.evolutionAt current).nextCurrent? = some next)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted current) (root.generatedLedgerAt current))
    (keys : Financial.Installation.KeepsKeys successor.ledgerEvolution)
    (entry : OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted current))) :
    (root.canonicalTargetEntryAtNext nextEq entry).1 = entry.1 := by
  revert keys successor
  unfold SourceNativeLedgerRootClosure.canonicalTargetEntryAtNext
  dsimp only [SourceNativeLedgerRootClosure.generatedLedgerAt] at *
  generalize_proofs at *
  generalize imageEq : root.source.ledgerCompiler.compile (root.emitted current) = image at *
  cases image with
  | nativeWrite write structural target evolution =>
    intro successor keys
    have targetEq : V.nativeTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact keys.1 entry
  | relationWrite write structural target evolution =>
    intro successor keys
    have targetEq : V.relationTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact keys.1 entry
  | continuedTransport write structural target evolution =>
    intro successor keys
    have targetEq : V.continuedTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact keys.1 entry
  | borromeanRedirect write structural target evolution =>
    intro successor keys
    have targetEq : V.redirectTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact keys.1 entry
  | faithfulTerminal terminal structural evolution =>
    intro successor _
    exact successor.elim

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)

theorem canonical_entry_is_the_same_installed_row :
    nextEntry frame visit (frame.entry visit.current) =
      frame.entry (nextVisit frame visit).current := by
  apply Financial.Installation.entry_eq_of_key _ _
  · exact (canonical_key frame.root.toAuthoritativeRoot.toLedgerRoot visit.current
      (frame.successor visit.current).targetCurrent (frame.successor visit.current).next_eq
      (frame.successor visit.current) (frame.successor_keys visit.current) (frame.entry visit.current)).trans
        (frame.family.entry_key _ _)
  · exact frame.family.open_fibres _

/-- The source keys identify the compiler-carried row with the already
installed inquiry row; this cast does not elect a new responsibility. -/
def nextAuthorityForInstalledEntry
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root (nextVisit frame visit)
      (frame.entry (nextVisit frame visit).current) :=
  canonical_entry_is_the_same_installed_row frame visit ▸
    nextAuthority frame visit (frame.entry visit.current) authority

#print axioms canonical_entry_is_the_same_installed_row
#print axioms nextAuthorityForInstalledEntry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action
