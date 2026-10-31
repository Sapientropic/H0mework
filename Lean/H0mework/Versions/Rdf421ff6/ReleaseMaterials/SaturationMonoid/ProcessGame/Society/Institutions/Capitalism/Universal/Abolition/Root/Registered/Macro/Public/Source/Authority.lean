import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.NativeEvolution

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
local notation "fibres" => family.open_fibres

def restructuringLaw : SourceNativeLedgerRestructuringLaw src :=
  identityOnlyWorldLedgerRestructuringLaw src
    (world.anchorAt family.currentSupport) family.open_fibres

private theorem patch_origin_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.origin entry).1) := by
  rw [patch_origin input depth count prefixLimit renewalLimit oldPast start family]
  exact Financial.Installation.keys_imply_origin_injective _ (Accounting.nativeEvolutionWithKeys input depth count prefixLimit renewalLimit oldPast start family current).property fibres

private theorem patch_destination_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.destination entry).1) := by
  rw [patch_destination input depth count prefixLimit renewalLimit oldPast start family]
  exact Financial.Installation.keys_imply_destination_injective _ (Accounting.nativeEvolutionWithKeys input depth count prefixLimit renewalLimit oldPast start family current).property fibres

def restructuringCertification {current : (V₀).Current}
    (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw input depth count prefixLimit renewalLimit oldPast start family)
      ((lc).compile occurrence) := by
  cases occurrence_eq_emitted input depth count prefixLimit renewalLimit oldPast start family occurrence
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> apply ExactLedgerRestructuringCertificationAt.ofInjective
  · exact patch_origin_injective input depth count prefixLimit renewalLimit oldPast start family current
  · exact patch_destination_injective input depth count prefixLimit renewalLimit oldPast start family current
  · exact patch_origin_injective input depth count prefixLimit renewalLimit oldPast start family current
  · exact patch_destination_injective input depth count prefixLimit renewalLimit oldPast start family current

def restructuringSource : SourceNativeRestructuringLedgerSource world V₀ where
  source := src
  compiler := {
    ledgerCompiler := lc
    restructuringLaw := restructuringLaw input depth count prefixLimit renewalLimit oldPast start family
    certifyRestructuring := restructuringCertification input depth count prefixLimit renewalLimit oldPast start family }


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
