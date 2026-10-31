import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Living
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
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
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "Cursor" => Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "advance" => Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

/-- A generated source frame may expose a native item or a lawful no-write
boundary. Its successor is read from that exact compiler image. -/
structure NativeFrame where
  nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none
  N : WorldRelationNetwork
  V : ConstructiveRoot.Vocabulary
  root : SourceNativeLivingRootClosure N V
  cursor : V.Current → Cursor
  successor : (current : V.Current) → SourceNativeLedgerGeneratedSuccessorAt
    (root.emitted current) (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current)
  next_exact : ∀ current, cursor (successor current).targetCurrent = advance (cursor current)
  entry : (current : V.Current) → OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted current))
  entries_finite : (current : V.Current) → Finite (OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted current)))
  open_fibres : ∀ support responsibility, Subsingleton (N.OpenAt support responsibility)
  successor_keys : ∀ current, Financial.Installation.KeepsKeys (successor current).ledgerEvolution

namespace Accounting

local notation "L" => livingRoot (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "lc" => ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def successor (current : Cursor) : SourceNativeLedgerGeneratedSuccessorAt
    (emit current) ((L).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) := by
  change SourceNativeLedgerGeneratedSuccessorAt (emit current) ((lc).compile (emit current))
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> exact PUnit.unit

theorem successor_current (current : Cursor) :
    (successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).targetCurrent = advance current := by
  have actual : ((source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).toRootSource.actual.compile
      (emit current)).nextCurrent? = some (advance current) := by
    rw [source_choice (review := review)]
    split <;> rfl
  exact Option.some.inj ((successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).next_eq.symm.trans actual)

theorem successor_keys (current : Cursor) : Financial.Installation.KeepsKeys
    (successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).ledgerEvolution := by
  have paidRows : Financial.Installation.KeepsKeys
      (patch (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).toLedgerWriteEvolution := by
    unfold Financial.Installation.KeepsKeys
    rw [patch_destination (review := review), patch_origin (review := review)]
    exact wholeEvolution_keeps_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  have all : ImageKeepsKeys ((lc).compile (emit current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact paidRows
  exact all _

def nativeFrame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition where
  N := N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  V := V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  root := L
  cursor := id
  successor := successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  next_exact := successor_current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  entry := owner (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  entries_finite := entries_finite (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  open_fibres := open_fibres (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  successor_keys := successor_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

end Accounting

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro
