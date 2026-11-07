import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Successor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {N : WorldRelationNetwork} (F : Flow N)



local notation "C" => F.Current
local notation "supp" => F.support
local notation "advance" => F.next
local notation "evolution" => F.evolution

local notation "src" => source F
local notation "emit" => emitted F
local notation "Seed" => RowSeed F
local notation "beforeRow" => sourceRow F
local notation "afterRow" => targetRow F
local notation "enumerate" => rowEnum F

local notation "V₀" => V F
local notation "rawRows" => RawRowAt F
local notation "rowCompiler" => rowSource F
local notation "wholePatch" => patch F
local notation "sourceWrites" => F.writes

local notation "lc" => ledgerCompiler F
local notation "lsrc" => ledgerSource F

local notation "root" => livingRoot F

def generatedRow (visit : SourceNativeTemporalVisitAt (root).toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt (N) (supp visit.current)) :
    ((root).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit).GeneratedEntryRowAt entry := by
  let compiler := ledgerCompiler F
  let occurrence := emitted F visit.current
  let selected := sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
    compiler.writeRowSource compiler.terminalRowSource (compiler.compile occurrence) (compiler.compilePatch occurrence) entry
  have present : selected.isSome = true := by
    let check (packet : Σ image : SourceNativeLedgerEvolutionAt _ occurrence,
        SourceNativeFiniteLedgerPatchAt _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource image) : Bool :=
      (sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
        compiler.writeRowSource compiler.terminalRowSource packet.1 packet.2 entry).isSome
    change check (sourcePacket F occurrence) = true
    dsimp only [occurrence, sourcePacket]
    split <;> rfl
  exact SourceNativeTemporalVisitGeneratedEvolutionAt.GeneratedEntryRowAt.ofSourceRow (selected.get present)

#print axioms generatedRow

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
