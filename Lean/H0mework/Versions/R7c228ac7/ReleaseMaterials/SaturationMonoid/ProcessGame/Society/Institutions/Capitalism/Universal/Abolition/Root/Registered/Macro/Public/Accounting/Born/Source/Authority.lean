import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Compiler
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Effects

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
local notation "keys" => whole_keys prior origin registered

def restructuringLaw : SourceNativeLedgerRestructuringLaw src :=
  identityOnlyWorldLedgerRestructuringLaw src
    ((Born.N prior origin registered).anchorAt (initialSupport prior origin registered)) (Born.family prior origin registered).open_fibres

private theorem patch_origin_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.origin entry).1) := by
  rw [patch_origin prior origin registered]
  exact Financial.Installation.keys_imply_origin_injective _ (keys current) (Born.family prior origin registered).open_fibres

private theorem patch_destination_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.destination entry).1) := by
  rw [patch_destination prior origin registered]
  exact Financial.Installation.keys_imply_destination_injective _ (keys current) (Born.family prior origin registered).open_fibres

def restructuringCertification {current : (V₀).Current}
    (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw prior origin registered)
      ((lc).compile occurrence) := by
  cases occurrence_eq_emitted prior origin registered occurrence
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> apply ExactLedgerRestructuringCertificationAt.ofInjective
  · exact patch_origin_injective prior origin registered current
  · exact patch_destination_injective prior origin registered current
  · exact patch_origin_injective prior origin registered current
  · exact patch_destination_injective prior origin registered current

def restructuringSource : SourceNativeRestructuringLedgerSource (Born.N prior origin registered) V₀ where
  source := src
  compiler := {
    ledgerCompiler := lc
    restructuringLaw := restructuringLaw prior origin registered
    certifyRestructuring := restructuringCertification prior origin registered }


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
