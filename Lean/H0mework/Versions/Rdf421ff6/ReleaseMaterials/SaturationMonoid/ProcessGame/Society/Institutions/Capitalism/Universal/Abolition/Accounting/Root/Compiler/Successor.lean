import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Living

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

def successor (current : F.Current) :
    SourceNativeLedgerGeneratedSuccessorAt (emit current)
      ((livingRoot F).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) := by
  change SourceNativeLedgerGeneratedSuccessorAt (emit current) ((lc).compile (emit current))
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> exact PUnit.unit

theorem successor_current (current : F.Current) :
    (successor F current).targetCurrent = advance current := by
  have actual : ((src).toRootSource.actual.compile (emit current)).nextCurrent? = some (advance current) := by
    rw [source_choice]
    split <;> rfl
  exact Option.some.inj
    ((successor F current).next_eq.symm.trans actual)

#print axioms successor_current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
