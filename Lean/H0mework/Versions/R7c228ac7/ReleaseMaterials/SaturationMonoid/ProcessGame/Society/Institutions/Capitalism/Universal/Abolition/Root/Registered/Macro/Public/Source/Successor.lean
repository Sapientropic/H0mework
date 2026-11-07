import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Living

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

local notation "C" => Accounting.Current input depth count anchor
local notation "supp" => Accounting.support input depth count family
local notation "advance" => Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start
local notation "evolution" => Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start family

local notation "src" => source input depth count prefixLimit renewalLimit oldPast start family
local notation "emit" => emitted input depth count prefixLimit renewalLimit oldPast start family
local notation "Seed" => RowSeed input depth count prefixLimit renewalLimit oldPast start family
local notation "beforeRow" => sourceRow input depth count prefixLimit renewalLimit oldPast start family
local notation "afterRow" => targetRow input depth count prefixLimit renewalLimit oldPast start family
local notation "enumerate" => rowEnum input depth count prefixLimit renewalLimit oldPast start family

local notation "V₀" => V input depth count prefixLimit renewalLimit oldPast start family
local notation "rawRows" => RawRowAt input depth count prefixLimit renewalLimit oldPast start family
local notation "rowCompiler" => rowSource input depth count prefixLimit renewalLimit oldPast start family
local notation "wholePatch" => patch input depth count prefixLimit renewalLimit oldPast start family
local notation "sourceWrites" => writes input depth count prefixLimit renewalLimit oldPast start

local notation "lc" => ledgerCompiler input depth count prefixLimit renewalLimit oldPast start family
local notation "lsrc" => ledgerSource input depth count prefixLimit renewalLimit oldPast start family

def successor (current : Accounting.Current input depth count anchor) :
    SourceNativeLedgerGeneratedSuccessorAt (emit current)
      ((livingRoot input depth count prefixLimit renewalLimit oldPast start family).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) := by
  change SourceNativeLedgerGeneratedSuccessorAt (emit current) ((lc).compile (emit current))
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> exact PUnit.unit

theorem successor_current (current : Accounting.Current input depth count anchor) :
    (successor input depth count prefixLimit renewalLimit oldPast start family current).targetCurrent = advance current := by
  have actual : ((src).toRootSource.actual.compile (emit current)).nextCurrent? = some (advance current) := by
    rw [source_choice]
    split <;> rfl
  exact Option.some.inj
    ((successor input depth count prefixLimit renewalLimit oldPast start family current).next_eq.symm.trans actual)

private def ImageKeepsKeys {base : WorldRelationNetwork} {vocabulary : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource base vocabulary} {current : vocabulary.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt occurrence image,
    Financial.Installation.KeepsKeys actual.ledgerEvolution

theorem successor_keys (current : Accounting.Current input depth count anchor) :
    Financial.Installation.KeepsKeys
      (successor input depth count prefixLimit renewalLimit oldPast start family current).ledgerEvolution := by
  have paidRows : Financial.Installation.KeepsKeys (wholePatch current).toLedgerWriteEvolution := by
    unfold Financial.Installation.KeepsKeys
    rw [patch_destination, patch_origin]
    exact (Accounting.nativeEvolutionWithKeys input depth count prefixLimit renewalLimit oldPast start family current).property
  have all : ImageKeepsKeys ((lc).compile (emit current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact paidRows
  exact all _

#print axioms successor_current
#print axioms successor_keys

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
