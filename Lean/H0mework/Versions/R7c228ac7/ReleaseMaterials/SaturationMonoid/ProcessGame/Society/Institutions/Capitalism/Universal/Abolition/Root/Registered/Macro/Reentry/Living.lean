import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.Compiler
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Component

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

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

local notation "src" => source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "V₀" => V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "lc" => ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "data" => rowsData (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "advance" => Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0

def restructuringLaw : SourceNativeLedgerRestructuringLaw src :=
  identityOnlyWorldLedgerRestructuringLaw src (world.anchorAt family.currentSupport) family.open_fibres

def restructuringCertification {current : (V₀).Current}
    (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq)
      ((lc).compile occurrence) := by
  cases occurrence_eq_emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq occurrence
  have keys := patch_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> exact ExactLedgerRestructuringCertificationAt.ofInjective
    (Financial.Installation.keys_imply_origin_injective _ keys family.open_fibres)
    (Financial.Installation.keys_imply_destination_injective _ keys family.open_fibres)

def restructuringSource : SourceNativeRestructuringLedgerSource world V₀ where
  source := src
  compiler := {
    ledgerCompiler := lc
    restructuringLaw := restructuringLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
    certifyRestructuring := restructuringCertification (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq }

inductive Projection
  | ledger | account | physical | sourceInput | sourceResult

def projectionLaw : SourceNativeProjectionLaw
    (ledgerSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq) where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {_current} occurrence _ => match projection with
    | .ledger => SourceNativeLedgerEvolutionAt src occurrence
    | .account => (Epoch.Finance.process input depth count).GeneratedState × (Epoch.Finance.process input depth count).GeneratedState
    | .physical => Actual.State (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument) (Port := Port)
    | .sourceInput => Mandatory.Report (review := review) input depth count prefixLimit renewalLimit start proposal
    | .sourceResult => Compile.Result input depth count prefixLimit renewalLimit
        (Physical.stateAt input depth count prefixLimit renewalLimit start.past)
        (Mandatory.executionRaw (review := review) input depth count prefixLimit renewalLimit start proposal)
  project := fun projection {current} occurrence _ => match projection with
    | .ledger => (lc).compile occurrence
    | .account => ⟨current.account, (advance current).account⟩
    | .physical => Accounting.physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 current
    | .sourceInput => Mandatory.produce (review := review) input depth count prefixLimit renewalLimit start proposal
    | .sourceResult => Physical.resultAt input depth count prefixLimit renewalLimit
        (Inventory.eventCursor (review := review) input depth count prefixLimit renewalLimit start proposal)

def authoritySource : SourceNativeAuthoritySource world V₀ where
  restructuringSource := restructuringSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (restructuringSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic world
  projectionLaw := projectionLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

def livingRoot : SourceNativeLivingRootClosure world V₀ where
  source := {
    base := authoritySource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
    terminalHandoff := (authoritySource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emit
  compiler_commutes := by
    intro current
    change ((lc).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry
