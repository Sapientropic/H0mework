import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Installed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

abbrev NativeTail (before after : (process input depth count).GeneratedState) :=
  Nonempty ((process input depth count).Run before.current after.current)

theorem appendTail {first middle last : (process input depth count).GeneratedState}
    (prior : NativeTail input depth count first middle)
    (later : NativeTail input depth count middle last) : NativeTail input depth count first last := by
  obtain ⟨left⟩ := prior
  exact later.map fun right => left.concatRuns (process input depth count) right

/-- A read/transport family for one existing financial world. New input
batches reuse this world and its actual account, rather than rebuilding it
from the original physical history. -/
structure AccountFamily (N : WorldRelationNetwork) (initial : (process input depth count).GeneratedState) where
  support : (account : (process input depth count).GeneratedState) →
    NativeTail input depth count initial account → N.Support
  owner : (account : (process input depth count).GeneratedState) →
    (native : NativeTail input depth count initial account) → OpenResponsibilityAt N (support account native)
  itemEvolution : (account : (process input depth count).GeneratedState) →
    (native : NativeTail input depth count initial account) → (item : ActualItem input depth count) →
    LedgerWriteEvolutionAt N ⟨support account native⟩
      ⟨support ((consume input depth count item account).next input depth count)
        (native.map fun prior => prior.concatRuns (process input depth count)
          ((consume input depth count item account).transition input depth count))⟩
  item_keys : ∀ account native item, Financial.Installation.KeepsKeys (itemEvolution account native item)
  entries_finite : ∀ account native, Finite (OpenResponsibilityAt N (support account native))
  open_fibres : ∀ support responsibility, Subsingleton (N.OpenAt support responsibility)
  entry : ∀ support, OpenResponsibilityAt N support
  entry_key : ∀ left right, (entry left).1 = (entry right).1
  disposition : ∀ support kind, N.DispositionAt support kind

namespace AccountFamily

variable {input depth count} {world : WorldRelationNetwork}
  {anchor : (process input depth count).GeneratedState}
  (family : AccountFamily input depth count world anchor)

abbrev N (_family : AccountFamily input depth count world anchor) := world
abbrev initial (_family : AccountFamily input depth count world anchor) := anchor

def currentSupport := family.support family.initial ⟨.nil⟩

/-- Re-anchoring is a restriction of the same family. It performs no native
step, admission, physical event, or account reconstruction. -/
def after (account : (process input depth count).GeneratedState)
    (native : NativeTail input depth count family.initial account) : AccountFamily input depth count world account where
  support := fun target later => family.support target (appendTail input depth count native later)
  owner := fun target later => family.owner target (appendTail input depth count native later)
  itemEvolution := fun target later item => family.itemEvolution target (appendTail input depth count native later) item
  item_keys := fun target later item => family.item_keys target (appendTail input depth count native later) item
  entries_finite := fun target later => family.entries_finite target (appendTail input depth count native later)
  open_fibres := family.open_fibres
  entry := family.entry
  entry_key := family.entry_key
  disposition := family.disposition

theorem after_keeps_the_literal_world_and_account
    (account : (process input depth count).GeneratedState)
    (native : NativeTail input depth count family.initial account) :
    (family.after account native).N = family.N ∧
      (family.after account native).initial = account ∧
      (family.after account native).currentSupport = family.support account native := ⟨rfl, rfl, rfl⟩

theorem every_item_carries_the_original_responsibility
    (account : (process input depth count).GeneratedState)
    (native : NativeTail input depth count family.initial account)
    (item : ActualItem input depth count)
    (entry : OpenResponsibilityAt family.N (family.support account native)) :
    ((family.itemEvolution account native item).destination entry).1.1 = entry.1 ∧
      ((family.itemEvolution account native item).destination entry).1.claim = entry.claim :=
  ⟨(family.item_keys account native item).1 entry,
    ((family.itemEvolution account native item).destination entry).2.toDebtLineage.claim_eq.symm⟩

end AccountFamily

#print axioms AccountFamily.after_keeps_the_literal_world_and_account
#print axioms AccountFamily.every_item_carries_the_original_responsibility

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation
