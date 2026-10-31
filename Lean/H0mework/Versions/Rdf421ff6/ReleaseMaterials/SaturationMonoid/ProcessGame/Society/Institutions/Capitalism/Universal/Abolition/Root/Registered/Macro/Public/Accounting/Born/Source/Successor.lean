import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Living

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)


local notation "C" => State origin registered
local notation "supp" => supportAt prior origin registered
local notation "advance" => next origin registered
local notation "evolution" => wholeEvolution prior origin registered

local notation "src" => source prior origin registered
local notation "emit" => emitted prior origin registered
local notation "Seed" => RowSeed prior origin registered
local notation "beforeRow" => sourceRow prior origin registered
local notation "afterRow" => targetRow prior origin registered
local notation "enumerate" => rowEnum prior origin registered

local notation "V₀" => V prior origin registered
local notation "rawRows" => RawRowAt prior origin registered
local notation "rowCompiler" => rowSource prior origin registered
local notation "wholePatch" => patch prior origin registered
local notation "sourceWrites" => writes origin registered

local notation "lc" => ledgerCompiler prior origin registered
local notation "lsrc" => ledgerSource prior origin registered

def successor (current : State origin registered) :
    SourceNativeLedgerGeneratedSuccessorAt (emit current)
      ((livingRoot prior origin registered).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) := by
  change SourceNativeLedgerGeneratedSuccessorAt (emit current) ((lc).compile (emit current))
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> exact PUnit.unit

theorem successor_current (current : State origin registered) :
    (successor prior origin registered current).targetCurrent = advance current := by
  have actual : ((src).toRootSource.actual.compile (emit current)).nextCurrent? = some (advance current) := by
    rw [source_choice]
    split <;> rfl
  exact Option.some.inj
    ((successor prior origin registered current).next_eq.symm.trans actual)

private def ImageKeepsKeys {base : WorldRelationNetwork} {vocabulary : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource base vocabulary} {current : vocabulary.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt occurrence image,
    Financial.Installation.KeepsKeys actual.ledgerEvolution

theorem successor_keys (current : State origin registered) :
    Financial.Installation.KeepsKeys
      (successor prior origin registered current).ledgerEvolution := by
  have paidRows : Financial.Installation.KeepsKeys (wholePatch current).toLedgerWriteEvolution := by
    unfold Financial.Installation.KeepsKeys
    rw [patch_destination, patch_origin]
    exact whole_keys prior origin registered current
  have all : ImageKeepsKeys ((lc).compile (emit current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact paidRows
  exact all _

#print axioms successor_current
#print axioms successor_keys

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
