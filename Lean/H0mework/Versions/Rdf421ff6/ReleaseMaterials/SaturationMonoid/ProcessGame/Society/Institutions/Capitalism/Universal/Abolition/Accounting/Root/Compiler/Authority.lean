import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Effects

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

def restructuringLaw : SourceNativeLedgerRestructuringLaw src :=
  identityOnlyWorldLedgerRestructuringLaw src
    (N.anchorAt (F.support F.initial)) F.open_fibres

private theorem patch_origin_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.origin entry).1) := by
  rw [patch_origin F]
  exact (F.injective current).1

private theorem patch_destination_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.destination entry).1) := by
  rw [patch_destination F]
  exact (F.injective current).2

def restructuringCertification {current : (V₀).Current}
    (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw F)
      ((lc).compile occurrence) := by
  cases occurrence_eq_emitted F occurrence
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> apply ExactLedgerRestructuringCertificationAt.ofInjective
  · exact patch_origin_injective F current
  · exact patch_destination_injective F current
  · exact patch_origin_injective F current
  · exact patch_destination_injective F current

def restructuringSource : SourceNativeRestructuringLedgerSource (N) V₀ where
  source := src
  compiler := {
    ledgerCompiler := lc
    restructuringLaw := restructuringLaw F
    certifyRestructuring := restructuringCertification F }


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
