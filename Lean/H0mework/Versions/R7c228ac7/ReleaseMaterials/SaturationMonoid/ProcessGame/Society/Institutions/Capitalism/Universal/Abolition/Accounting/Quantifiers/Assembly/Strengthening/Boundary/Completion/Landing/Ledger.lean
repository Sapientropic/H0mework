import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.World

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev oldSupport (support : N.Support) : (W root boundary).Support := (support,false)

def readOld {support : N.Support} :
    OpenResponsibilityAt (W root boundary) (oldSupport root boundary support) → OpenResponsibilityAt N support
  | ⟨.inl key,opened⟩ => ⟨key,opened⟩
  | ⟨.inr _,opened⟩ => nomatch opened

theorem readOld_oldRow {support : N.Support} (row : OpenResponsibilityAt N support) :
    readOld root boundary (oldRow root boundary false row) = row := rfl

theorem oldRow_readOld {support : N.Support}
    (row : OpenResponsibilityAt (W root boundary) (oldSupport root boundary support)) :
    oldRow root boundary false (readOld root boundary row) = row := by
  rcases row with ⟨key,opened⟩
  cases key with
  | inl _ => rfl
  | inr _ => exact nomatch opened

def oldPresentation (support : N.Support) : ConstructivePresentation
    (OpenResponsibilityAt N support)
    (OpenResponsibilityAt (W root boundary) (oldSupport root boundary support)) where
  forward := oldRow root boundary false
  backward := readOld root boundary
  forward_backward := oldRow_readOld root boundary
  backward_forward := readOld_oldRow root boundary

def liftEntry {before after : N.Support} {source : OpenResponsibilityAt N before}
    {target : OpenResponsibilityAt N after} (actual : LedgerEntryEvolutionAt N source target) :
    LedgerEntryEvolutionAt (W root boundary)
      (oldRow root boundary false source) (oldRow root boundary false target) := by
  cases actual with
  | carried supportEq entryEq =>
      cases supportEq
      cases entryEq
      exact .carried rfl (HEq.rfl)
  | maintained anchor incidence lineage key claim debit =>
      exact .maintained anchor incidence lineage (congrArg Sum.inl key) claim debit
  | transferred receipt lineage claim budget =>
      exact .transferred (.inl receipt) lineage claim budget

def liftLedger {before after : CompleteLiveLedgerAt N}
    (actual : LedgerWriteEvolutionAt N before after) :
    LedgerWriteEvolutionAt (W root boundary)
      ⟨oldSupport root boundary before.support⟩ ⟨oldSupport root boundary after.support⟩ where
  destination := fun row =>
    let selected := actual.destination (readOld root boundary row)
    ⟨oldRow root boundary false selected.1,
      by
        have receipt := liftEntry root boundary selected.2
        rw [oldRow_readOld root boundary row] at receipt
        exact receipt⟩
  origin := fun row =>
    let selected := actual.origin (readOld root boundary row)
    ⟨oldRow root boundary false selected.1,
      by
        have receipt := liftEntry root boundary selected.2
        rw [oldRow_readOld root boundary row] at receipt
        exact receipt⟩

theorem liftLedger_destination {before after : CompleteLiveLedgerAt N}
    (actual : LedgerWriteEvolutionAt N before after) (row : before.Entry) :
    ((liftLedger root boundary actual).destination (oldRow root boundary false row)).1 =
      oldRow root boundary false (actual.destination row).1 := rfl

theorem liftLedger_origin {before after : CompleteLiveLedgerAt N}
    (actual : LedgerWriteEvolutionAt N before after) (row : after.Entry) :
    ((liftLedger root boundary actual).origin (oldRow root boundary false row)).1 =
      oldRow root boundary false (actual.origin row).1 := rfl

def liftTerminal {before : CompleteLiveLedgerAt N} (actual : LedgerTerminalEvolutionAt N before) :
    LedgerTerminalEvolutionAt (W root boundary) ⟨oldSupport root boundary before.support⟩ where
  discharge := fun row => ⟨(actual.discharge (readOld root boundary row)).receipt⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
