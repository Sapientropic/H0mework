import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.Living

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

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
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  {review : Option (ReviewPhase.ContextAt input)}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (seed_eq : Accounting.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 = anchor)

local notation "L" => livingRoot (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "V₀" => V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "lc" => ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "advance" => Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0

def successor (current : (V₀).Current) : SourceNativeLedgerGeneratedSuccessorAt
    (emit current) ((L).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) := by
  change SourceNativeLedgerGeneratedSuccessorAt (emit current) ((lc).compile (emit current))
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> exact PUnit.unit

theorem successor_current (current : (V₀).Current) :
    (successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current).targetCurrent = advance current := by
  have actual : ((source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).toRootSource.actual.compile
      (emit current)).nextCurrent? = some (advance current) := by
    rw [source_choice]
    split <;> rfl
  exact Option.some.inj ((successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current).next_eq.symm.trans actual)

theorem successor_keys (current : (V₀).Current) : Financial.Installation.KeepsKeys
    (successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current).ledgerEvolution := by
  have all : ImageKeepsKeys ((lc).compile (emit current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact patch_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current
  exact all _

def nativeFrame : Macro.NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 where
  N := world
  V := V₀
  root := L
  cursor := id
  successor := successor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
  next_exact := successor_current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
  entry := fun current => family.entry (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current)
  entries_finite := fun current => family.entries_finite current.account
    (nativeTail (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal seed_eq current)
  open_fibres := family.open_fibres
  successor_keys := successor_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

def basis : Inquiry.Basis world where
  entry := family.entry
  disposition := family.disposition

def activeFrame := Inquiry.installFrame
  (nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq)
  (basis input depth count family)

def activeInstallation := Inquiry.installation
  (nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq)
  (basis input depth count family)

theorem the_next_batch_keeps_the_literal_world :
    (activeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).N = world := rfl

theorem the_next_batch_starts_at_the_existing_support :
    (activeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).sourceSupport
      (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0) = family.currentSupport :=
  initial_support_is_the_same_current_world (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.nativeFrame
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.activeFrame
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.the_next_batch_starts_at_the_existing_support
