import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Compiler
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "W" => N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "V₀" => V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "src" => source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "lc" => ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "wholePatch" => patch (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "fibres" => open_fibres (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "keys" => wholeEvolution_keeps_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def restructuringLaw : SourceNativeLedgerRestructuringLaw src :=
  identityOnlyWorldLedgerRestructuringLaw src
    ((W).anchorAt (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition))) fibres

private theorem patch_origin_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.origin entry).1) := by
  rw [patch_origin (review := review)]
  exact Financial.Installation.keys_imply_origin_injective _ (keys current) fibres

private theorem patch_destination_injective (current : (V₀).Current) :
    Function.Injective (fun entry => ((wholePatch current).toLedgerWriteEvolution.destination entry).1) := by
  rw [patch_destination (review := review)]
  exact Financial.Installation.keys_imply_destination_injective _ (keys current) fibres

def restructuringCertification {current : (V₀).Current}
    (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
      ((lc).compile occurrence) := by
  cases occurrence_eq_emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition occurrence
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> apply ExactLedgerRestructuringCertificationAt.ofInjective
  · exact patch_origin_injective (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  · exact patch_destination_injective (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  · exact patch_origin_injective (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  · exact patch_destination_injective (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current

def restructuringSource : SourceNativeRestructuringLedgerSource W V₀ where
  source := src
  compiler := {
    ledgerCompiler := lc
    restructuringLaw := restructuringLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
    certifyRestructuring := restructuringCertification (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
