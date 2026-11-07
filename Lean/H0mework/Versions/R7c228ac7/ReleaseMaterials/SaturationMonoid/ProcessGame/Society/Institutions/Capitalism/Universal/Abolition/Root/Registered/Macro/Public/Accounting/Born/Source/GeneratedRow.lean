import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Successor

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

local notation "root" => livingRoot prior origin registered

def generatedRow (visit : SourceNativeTemporalVisitAt (root).toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt (Born.N prior origin registered) (supp visit.current)) :
    ((root).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit).GeneratedEntryRowAt entry := by
  let compiler := ledgerCompiler prior origin registered
  let occurrence := emitted prior origin registered visit.current
  let selected := sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
    compiler.writeRowSource compiler.terminalRowSource (compiler.compile occurrence) (compiler.compilePatch occurrence) entry
  have present : selected.isSome = true := by
    let check (packet : Σ image : SourceNativeLedgerEvolutionAt _ occurrence,
        SourceNativeFiniteLedgerPatchAt _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource image) : Bool :=
      (sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
        compiler.writeRowSource compiler.terminalRowSource packet.1 packet.2 entry).isSome
    change check (sourcePacket prior origin registered occurrence) = true
    dsimp only [occurrence, sourcePacket]
    split <;> rfl
  exact SourceNativeTemporalVisitGeneratedEvolutionAt.GeneratedEntryRowAt.ofSourceRow (selected.get present)

#print axioms generatedRow

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
